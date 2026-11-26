-- Prove2me | solution 1 for DirectedHamiltonicity.Main.parity_target_length_guard
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:23:39.796682+00:00
-- url     : https://prove2.me/submissions/ab7594f0-cf6e-40b8-ad03-532d61979bd3

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms


namespace RamCost
open TargetedSamplers

abbrev Memory := ℕ → ℕ

/-- A fragment occurs at an address in a larger, unmodified program. -/
def Located (p : Program) (pc : ℕ) (code : Program) : Prop :=
  ∀ i, i < code.length → p[pc + i]? = code[i]?

theorem Located.atAppend (before code after : Program) :
    Located (before ++ code ++ after) before.length code := by
  intro i hi
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simpa using List.getElem?_append_left (l₂ := after) hi

theorem Located.head {p : Program} {pc : ℕ} {i : Instr} {rest : Program}
    (h : Located p pc (i :: rest)) : p[pc]? = some i := by
  simpa using h 0 (by simp)

theorem Located.tail {p : Program} {pc : ℕ} {i : Instr} {rest : Program}
    (h : Located p pc (i :: rest)) : Located p (pc+1) rest := by
  intro j hj
  simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j+1) (by simpa using hj)

theorem Located.ofLookup {p code : Program} {pc : ℕ}
    (h : ∀ i (hi : i < code.length), p[pc+i]? = some code[i]) :
    Located p pc code := by
  intro i hi
  rw [h i hi, List.getElem?_eq_getElem hi]

/-- Straight-line instructions with one memory destination. Each constructor emits one
instruction of the upstream machine. Register operands are addresses of work cells. -/
inductive Op
  | lit (d value : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | load (d a : ℕ)
  | store (a b : ℕ)
  | inputLength (d : ℕ)
  | readInput (d a : ℕ)
  | readCoin (d a : ℕ)
  deriving Repr

namespace Op
def instr : Op → Instr
  | .lit d k => .const d k
  | .add d a b => .add d a b
  | .sub d a b => .monus d a b
  | .load d a => .load d a
  | .store a b => .store a b
  | .inputLength d => .inputLength d
  | .readInput d a => .readInput d a
  | .readCoin d a => .readCoin d a

def dest (m : Memory) : Op → ℕ
  | .lit d _ | .add d _ _ | .sub d _ _ | .load d _ | .inputLength d | .readInput d _ | .readCoin d _ => d
  | .store a _ => m a

def value (τ : Tapes) (m : Memory) : Op → ℕ
  | .lit _ k => k
  | .add _ a b => m a + m b
  | .sub _ a b => m a - m b
  | .load _ a => m (m a)
  | .store _ b => m b
  | .inputLength _ => τ.input.length
  | .readInput _ a => bitVal τ.input[m a]?
  | .readCoin _ a => bitVal τ.coins[m a]?

def effect (o : Op) (τ : Tapes) (m : Memory) : Memory :=
  Function.update m (o.dest m) (o.value τ m)

/-- Exact upstream log-cost, including the widths of direct register addresses. -/
def cost (τ : Tapes) (m : Memory) : Op → ℕ
  | .lit d k => 1 + d.size + k.size
  | .add d a b => 1 + d.size + a.size + b.size + (m a).size + (m b).size + (m a + m b).size
  | .sub d a b => 1 + d.size + a.size + b.size + (m a).size + (m b).size + (m a - m b).size
  | .load d a => 1 + d.size + a.size + (m a).size + (m (m a)).size
  | .store a b => 1 + a.size + b.size + (m a).size + (m b).size
  | .inputLength d => 1 + d.size + τ.input.length.size
  | .readInput d a => 1 + d.size + a.size + (m a).size + (bitVal τ.input[m a]?).size
  | .readCoin d a => 1 + d.size + a.size + (m a).size + (bitVal τ.coins[m a]?).size

theorem step_eq (o : Op) (p : Program) (τ : Tapes) (s : State)
    (live : s.halted = false) (atPc : p[s.pc]? = some o.instr) :
    p.step τ s = { s.write (o.dest s.mem) (o.value τ s.mem) with
      pc := s.pc+1, work := s.work + o.cost τ s.mem } := by
  cases o <;> simp [Program.step, instr, dest, value, cost, live, atPc, Nat.add_assoc] at *

end Op

abbrev Block := List Op
namespace Block

def code (b : Block) : Program := b.map Op.instr

def effect (τ : Tapes) : Block → Memory → Memory
  | [], m => m
  | o :: b, m => effect τ b (o.effect τ m)

def cost (τ : Tapes) : Block → Memory → ℕ
  | [], _ => 0
  | o :: b, m => o.cost τ m + cost τ b (o.effect τ m)

@[simp] theorem code_length (b : Block) : (code b).length = b.length := by simp [code]

@[simp] theorem effect_append (τ : Tapes) (a b : Block) (m : Memory) :
    effect τ (a ++ b) m = effect τ b (effect τ a m) := by
  induction a generalizing m with
  | nil => rfl
  | cons o a ih => exact ih _

@[simp] theorem cost_append (τ : Tapes) (a b : Block) (m : Memory) :
    cost τ (a ++ b) m = cost τ a m + cost τ b (effect τ a m) := by
  induction a generalizing m with
  | nil => simp [cost, effect]
  | cons o a ih => simp [cost, effect, ih, Nat.add_assoc]

/-- Observable postcondition for a straight-line block. The upstream state also keeps
its own touched-cell set and peak widths throughout execution. -/
structure Post (b : Block) (τ : Tapes) (s t : State) : Prop where
  pc : t.pc = s.pc + b.length
  live : t.halted = false
  mem : t.mem = effect τ b s.mem
  work : t.work = s.work + cost τ b s.mem
  out : t.out = s.out
  bot : t.bot = s.bot
  cursor : t.wcursor = s.wcursor
  queries : t.asked = s.asked

theorem sound (b : Block) (p : Program) (τ : Tapes) (s : State)
    (live : s.halted = false) (loc : Located p s.pc (code b)) :
    Post b τ s ((p.step τ)^[b.length] s) := by
  induction b generalizing s with
  | nil => exact ⟨rfl, live, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons o b ih =>
    have step := o.step_eq p τ s live loc.head
    have loc' : Located p (p.step τ s).pc (code b) := by rw [step]; exact loc.tail
    have h := ih (p.step τ s) (by rw [step]; exact live) loc'
    simp only [List.length_cons, Function.iterate_succ_apply]
    obtain ⟨pc, live', mem, work, out, bot, cursor, queries⟩ := h
    rw [step] at pc live' mem work out bot cursor queries ⊢
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1] using pc, live', mem,
      by simpa [cost, Op.effect, State.write, Nat.add_assoc] using work, out, bot, cursor, queries⟩

end Block

/-- Turn an arbitrary halting trace into the upstream machine's canonical final state. -/
theorem final_of_halted {p : Program} {τ : Tapes} {k : ℕ}
    (h : (p.config τ k).halted = true) : p.final τ = some (p.config τ k) := by
  have ex : ∃ i, (p.config τ i).halted = true := ⟨k,h⟩
  have hm := Nat.find_spec ex
  have hk := Nat.find_min' ex h
  have fixed : p.step τ (p.config τ (Nat.find ex)) = p.config τ (Nat.find ex) := by
    simp [Program.step, hm]
  have he : p.config τ k = p.config τ (Nat.find ex) := by
    conv_lhs => rw [show k = (k - Nat.find ex) + Nat.find ex by omega]
    exact Function.iterate_add_apply .. |>.trans (Function.iterate_fixed fixed _)
  simp only [Program.final, dif_pos ex, he]

end RamCost

namespace RamCost
open TargetedSamplers

/-- A finite trace between two states of the same program. -/
def Reaches (p : Program) (τ : Tapes) (s t : State) : Prop :=
  ∃ k, (p.step τ)^[k] s = t

namespace Reaches
theorem refl (p : Program) (τ : Tapes) (s : State) : Reaches p τ s s := ⟨0,rfl⟩

theorem one (p : Program) (τ : Tapes) (s : State) : Reaches p τ s (p.step τ s) := ⟨1,rfl⟩

theorem trans {p : Program} {τ : Tapes} {s t u : State}
    (a : Reaches p τ s t) (b : Reaches p τ t u) : Reaches p τ s u := by
  obtain ⟨i,rfl⟩ := a
  obtain ⟨j,rfl⟩ := b
  exact ⟨j+i, Function.iterate_add_apply ..⟩

theorem runsIn {p : Program} {τ : Tapes} {s : State} {t : ℕ} {v : Option (List Bool)}
    (h : Reaches p τ State.init s) (halt : s.halted = true)
    (time : s.work ≤ t) (result : s.result = v) : p.RunsIn τ t v := by
  obtain ⟨k,rfl⟩ := h
  exact ⟨_, final_of_halted (k := k) halt, time, result⟩
end Reaches

def jumpCost (a b target : ℕ) (m : Memory) : ℕ :=
  1 + a.size + b.size + (m a).size + (m b).size + target.size

theorem step_jump {p : Program} {τ : Tapes} {s : State} {a b target : ℕ}
    (live : s.halted = false) (atPc : p[s.pc]? = some (.jle a b target)) :
    p.step τ s = {s with
      pc := if s.mem a ≤ s.mem b then target else s.pc+1
      work := s.work + jumpCost a b target s.mem} := by
  simp [Program.step, live, atPc, jumpCost, Nat.add_assoc]

/-- Emit a relocatable loop: while mem[index] < mem[limit], execute body.
Absolute branch targets are generated from the eventual entry address. -/
def whileLT (pc index limit : ℕ) (body : Block) : Program :=
  [.jle limit index (pc + body.length + 2)] ++ Block.code body ++ [.jle index index pc]

/-- The loop rule needs a decreasing natural variant, a memory invariant and an
upper bound on each iteration. Boundary tests and back edges pay real log-cost. -/
theorem whileLT_rule {p : Program} {τ : Tapes} {entry index limit : ℕ} {body : Block}
    {inv : ℕ → Memory → Prop} {per exitCost : ℕ}
    (loc : Located p entry (whileLT entry index limit body))
    (exit : ∀ m, inv 0 m → m limit ≤ m index ∧
      jumpCost limit index (entry+body.length+2) m ≤ exitCost)
    (next : ∀ k m, inv (k+1) m → m index < m limit ∧
      inv k (Block.effect τ body m) ∧
      jumpCost limit index (entry+body.length+2) m + Block.cost τ body m +
        jumpCost index index entry (Block.effect τ body m) ≤ per)
    (k : ℕ) (s : State) (pc : s.pc = entry) (live : s.halted = false)
    (hs : inv k s.mem) :
    ∃ t, Reaches p τ s t ∧ t.pc = entry+body.length+2 ∧ t.halted = false ∧
      inv 0 t.mem ∧ t.work ≤ s.work + k*per + exitCost ∧ t.out = s.out ∧ t.bot = s.bot := by
  have head : p[entry]? = some (.jle limit index (entry+body.length+2)) := loc.head
  have mid : Located p (entry+1) (Block.code body) := by
    intro j hj
    have h := loc.tail j (by simpa [whileLT] using (show j < (Block.code body).length+1 by omega))
    change p[entry+1+j]? = (Block.code body ++ [.jle index index entry])[j]? at h
    rwa [List.getElem?_append_left hj] at h
  have back : p[entry+1+body.length]? = some (.jle index index entry) := by
    have h := loc.tail body.length (by simp [Block.code])
    simpa [whileLT, Block.code, List.getElem?_append] using h
  induction k generalizing s with
  | zero =>
    obtain ⟨done, bound⟩ := exit _ hs
    have fetch : p[s.pc]? = some (.jle limit index (entry+body.length+2)) := by rw [pc]; exact head
    have e := step_jump (τ := τ) live fetch
    rw [if_pos done] at e
    refine ⟨_, Reaches.one p τ s, ?_⟩
    rw [e]
    exact ⟨rfl, live, hs, by simpa using Nat.add_le_add_left bound s.work, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨more, preserve, bound⟩ := next k _ hs
    let u := p.step τ s
    have fetch : p[s.pc]? = some (.jle limit index (entry+body.length+2)) := by rw [pc]; exact head
    have eu : u = {s with
        pc := entry+1
        work := s.work + jumpCost limit index (entry+body.length+2) s.mem} := by
      simpa [pc, Nat.not_le.mpr more] using step_jump (τ := τ) live fetch
    let v := (p.step τ)^[body.length] u
    have hv : Block.Post body τ u v := Block.sound body p τ u (by rw [eu]; exact live)
      (by rw [eu]; exact mid)
    have vp : v.pc = entry+1+body.length := by rw [hv.pc, eu]
    let z := p.step τ v
    have ez : z = {v with pc := entry, work := v.work + jumpCost index index entry v.mem} := by
      have fetchBack : p[v.pc]? = some (.jle index index entry) := by rw [vp]; exact back
      simpa using step_jump (τ := τ) hv.live fetchBack
    obtain ⟨t, reach, hp, hl, hi, ht, ho, hb⟩ := ih z (by rw [ez]) (by rw [ez]; exact hv.live)
      (by rw [ez]; change inv k v.mem; rw [hv.mem, eu]; exact preserve)
    refine ⟨t, ((Reaches.one p τ s).trans ((show Reaches p τ u v from ⟨_,rfl⟩).trans
      (Reaches.one p τ v))).trans reach, hp, hl, hi, ?_, ?_, ?_⟩
    · rw [ez] at ht
      change v.work + jumpCost index index entry v.mem + k*per + exitCost ≥ t.work at ht
      rw [hv.work, hv.mem, eu] at ht
      simp only [Nat.succ_mul] at *
      omega
    · rw [ho, ez]; change v.out = s.out; rw [hv.out, eu]
    · rw [hb, ez]; change v.bot = s.bot; rw [hv.bot, eu]

/-- Output one Boolean (zero encodes false) and halt. Includes the last two
instructions in the claimed running time. -/
theorem outputHalt {p : Program} {τ : Tapes} {r : ℕ} {s : State}
    (live : s.halted = false) (loc : Located p s.pc [.output r, .halt])
    (reach : Reaches p τ State.init s) (bot : s.bot = false) :
    p.RunsIn τ (s.work + (1+r.size+(s.mem r).size) + 1)
      (some (s.out ++ [s.mem r != 0])) := by
  let t := p.step τ s
  have et : t = {s with
      pc := s.pc+1
      out := s.out ++ [s.mem r != 0]
      work := s.work + (1+r.size+(s.mem r).size)} := by
    simp [t, Program.step, live, loc.head, Nat.add_assoc]
  have endAt : p[t.pc]? = some .halt := by rw [et]; exact loc.tail.head
  have e : p.step τ t = {t with halted := true, work := t.work + 1} := by
    have l : t.halted = false := by rw [et]; exact live
    simp [Program.step, l, endAt]
  apply ((reach.trans (Reaches.one p τ s)).trans (Reaches.one p τ t)).runsIn
  · rw [e]
  · rw [e, et]
  · rw [e, et]; simp [State.result, bot]

/-- Any verified straight-line block can itself be made a closed Boolean program. -/
def Block.withOutput (b : Block) (r : ℕ) : Program := Block.code b ++ [.output r, .halt]

theorem Block.runsIn (b : Block) (τ : Tapes) (r : ℕ) :
    let m := Block.effect τ b State.init.mem
    (b.withOutput r).RunsIn τ (Block.cost τ b State.init.mem + (1+r.size+(m r).size) + 1)
      (some [m r != 0]) := by
  let p := b.withOutput r
  let s := (p.step τ)^[b.length] State.init
  have loc : Located p State.init.pc (Block.code b) := Located.atAppend [] _ _
  have h : Block.Post b τ State.init s := b.sound p τ _ rfl loc
  have ending : Located p s.pc [.output r, .halt] := by
    rw [h.pc]; simpa [State.init, Block.withOutput, p] using
      Located.atAppend (Block.code b) [.output r, .halt] []
  have f := outputHalt h.live ending (show Reaches p τ State.init s from ⟨_,rfl⟩)
    (by rw [h.bot]; rfl)
  simpa [h.work, h.mem, h.out, State.init, p] using f

end RamCost

namespace RamCost
open TargetedSamplers

variable {p : Program} {τ : Tapes} {pc : ℕ} {a b : Program}

theorem Located.left (h : Located p pc (a++b)) : Located p pc a := by
  intro i hi
  have e := h i (by simp; omega)
  rwa [List.getElem?_append_left hi] at e

theorem Located.right (h : Located p pc (a++b)) : Located p (pc+a.length) b := by
  intro i hi
  have e := h (a.length+i) (by simpa using hi)
  simpa [List.getElem?_append_right (by omega : a.length ≤ a.length+i), Nat.add_assoc] using e

/-- Specification for a fragment with a single exit. Cost is the exact change
in the machine work counter. The actual number of steps may vary by trace. -/
def Realizes (p : Program) (τ : Tapes) (entry : ℕ) (m : Memory)
    (exit : ℕ) (m' : Memory) (cost : ℕ) : Prop :=
  ∀ s : State, s.pc = entry → s.mem = m → s.halted = false →
    ∃ t, Reaches p τ s t ∧ t.pc = exit ∧ t.mem = m' ∧ t.work = s.work+cost ∧
      t.halted = false ∧ t.out = s.out ∧ t.bot = s.bot

theorem Realizes.seq {i j k x y : ℕ} {m n u : Memory}
    (h : Realizes p τ i m j n x) (g : Realizes p τ j n k u y) :
    Realizes p τ i m k u (x+y) := by
  intro s pc mem live
  obtain ⟨t,st,tp,tm,tw,tl,tout,tbot⟩ := h s pc mem live
  obtain ⟨v,tv,vp,vm,vw,vl,vout,vbot⟩ := g t tp tm tl
  exact ⟨v,st.trans tv,vp,vm,by rw [vw,tw,Nat.add_assoc],vl,vout.trans tout,vbot.trans tbot⟩

theorem Realizes.block {ops : Block} (h : Located p pc (Block.code ops)) (m : Memory) :
    Realizes p τ pc m (pc+ops.length) (Block.effect τ ops m) (Block.cost τ ops m) := by
  intro s sp sm live
  subst pc m
  have t := Block.sound ops p τ s live h
  exact ⟨_, ⟨_,rfl⟩, t.pc, t.mem, t.work, t.live, t.out, t.bot⟩

theorem Realizes.jump {a b dest : ℕ} (h : p[pc]? = some (.jle a b dest)) (m : Memory) :
    Realizes p τ pc m (if m a ≤ m b then dest else pc+1) m (jumpCost a b dest m) := by
  intro s sp sm live
  subst pc m
  have t := step_jump (τ := τ) live h
  exact ⟨_, Reaches.one p τ s, by rw [t], by rw [t], by rw [t], by rw [t]; exact live,
    by rw [t], by rw [t]⟩

/-- Structured programs on registers. Only the compiler assigns absolute jump targets. -/
inductive Cmd
  | block (ops : Block)
  | seq (first second : Cmd)
  | ifLE (a b : ℕ) (yes no : Cmd)
  | whileLT (index limit : ℕ) (body : Cmd)
  deriving Repr

namespace Cmd

def len : Cmd → ℕ
  | .block ops => ops.length
  | .seq c d => c.len + d.len
  | .ifLE _ _ yes no => 1 + no.len + 1 + yes.len
  | .whileLT _ _ body => body.len + 2

def emit : Cmd → ℕ → Program
  | .block b, _ => b.code
  | .seq c d, pc => c.emit pc ++ d.emit (pc+c.len)
  | .ifLE a b y n, pc =>
    .jle a b (pc+1+n.len+1) :: (n.emit (pc+1) ++
      (.jle a a (pc+1+n.len+1+y.len) :: y.emit (pc+1+n.len+1)))
  | .whileLT i l body, pc =>
    .jle l i (pc+body.len+2) :: (body.emit (pc+1) ++ [.jle i i pc])

@[simp] theorem emit_length (c : Cmd) (pc : ℕ) : (c.emit pc).length = c.len := by
  induction c generalizing pc <;> (simp_all [emit, len]; try omega)

/-- Finite evaluation derivations. Exact branch cost depends on layout, on the branch
taken, and on the registers at that point. Diverging loops have no finite derivation. -/
inductive Eval (τ : Tapes) : Cmd → ℕ → Memory → Memory → ℕ → Prop
  | block (ops : Block) (pc : ℕ) (m : Memory) :
    Eval τ (.block ops) pc m (Block.effect τ ops m) (Block.cost τ ops m)
  | seq {c d pc m u v x y} :
    Eval τ c pc m u x → Eval τ d (pc+c.len) u v y → Eval τ (.seq c d) pc m v (x+y)
  | yes {a b y n pc m v x} : m a ≤ m b → Eval τ y (pc+1+n.len+1) m v x →
    Eval τ (.ifLE a b y n) pc m v (jumpCost a b (pc+1+n.len+1) m + x)
  | no {a b y n pc m v x} : m b < m a → Eval τ n (pc+1) m v x →
    Eval τ (.ifLE a b y n) pc m v
      ((jumpCost a b (pc+1+n.len+1) m + x) + jumpCost a a (pc+1+n.len+1+y.len) v)
  | done {i l body pc m} : m l ≤ m i →
    Eval τ (.whileLT i l body) pc m m (jumpCost l i (pc+body.len+2) m)
  | more {i l body pc m u v x y} : m i < m l → Eval τ body (pc+1) m u x →
    Eval τ (.whileLT i l body) pc u v y →
    Eval τ (.whileLT i l body) pc m v
      (((jumpCost l i (pc+body.len+2) m + x) + jumpCost i i pc u) + y)

theorem Eval.sound {c : Cmd} {entry cost : ℕ} {m v : Memory} (ev : Eval τ c entry m v cost)
    (loc : Located p entry (c.emit entry)) :
    Realizes p τ entry m (entry+c.len) v cost := by
  induction ev with
  | block ops pc m => exact Realizes.block loc m
  | @seq c d pc m u v x y hc hd ihc ihd =>
    have l := (show Located p pc (c.emit pc ++ d.emit (pc+c.len)) from loc)
    have r := l.right
    rw [emit_length] at r
    simpa [len, Nat.add_assoc] using (ihc l.left).seq (ihd r)
  | @yes a b y n pc m v x cmp _ ih =>
    have split := loc.tail
    have tail := split.right
    rw [emit_length] at tail
    have j := Realizes.jump (τ := τ) loc.head m
    rw [if_pos cmp] at j
    simpa [len, Nat.add_assoc] using j.seq (ih tail.tail)
  | @no a b y n pc m v x cmp _ ih =>
    have split := loc.tail
    have tail := split.right
    rw [emit_length] at tail
    have j := Realizes.jump (τ := τ) loc.head m
    rw [if_neg (Nat.not_le.mpr cmp)] at j
    have back := Realizes.jump (τ := τ) tail.head v
    rw [if_pos (Nat.le_refl _)] at back
    simpa [len, Nat.add_assoc] using
      (j.seq (ih split.left)).seq back
  | @done i l body pc m cmp =>
    have j := Realizes.jump (τ := τ) loc.head m
    rw [if_pos cmp] at j
    simpa [len, Nat.add_assoc] using j
  | @more i l body pc m u v x y cmp _ _ ihBody ihLoop =>
    have split := loc.tail
    have tail := split.right
    rw [emit_length] at tail
    have j := Realizes.jump (τ := τ) loc.head m
    rw [if_neg (Nat.not_le.mpr cmp)] at j
    have back := Realizes.jump (τ := τ) tail.head u
    rw [if_pos (Nat.le_refl _)] at back
    exact ((j.seq (ihBody split.left)).seq back).seq (ihLoop loc)

end Cmd
end RamCost

namespace RamCost.Cmd
open TargetedSamplers

/-- Existence of a finite execution within a budget and satisfying a postcondition. -/
def Ensures (τ : Tapes) (c : Cmd) (pc : ℕ) (m : Memory) (budget : ℕ)
    (post : Memory → Prop) : Prop :=
  ∃ v cost, Eval τ c pc m v cost ∧ cost ≤ budget ∧ post v

theorem Ensures.weaken {τ c pc m a b} {P Q : Memory → Prop}
    (h : Ensures τ c pc m a P) (time : a ≤ b) (post : ∀ v, P v → Q v) :
    Ensures τ c pc m b Q := by
  obtain ⟨v,k,hk,le,hv⟩ := h
  exact ⟨v,k,hk,le.trans time,post v hv⟩

theorem Ensures.seq {τ a b pc m x y} {P Q : Memory → Prop}
    (h : Ensures τ a pc m x P) (g : ∀ u, P u → Ensures τ b (pc+a.len) u y Q) :
    Ensures τ (.seq a b) pc m (x+y) Q := by
  obtain ⟨u,k,e,lk,hu⟩ := h
  obtain ⟨v,l,f,ll,hv⟩ := g u hu
  exact ⟨v,k+l,.seq e f,Nat.add_le_add lk ll,hv⟩

/-- Upper-bound loop rule for any nested, structured body. The toll includes both
conditional and unconditional jumps. The variant counts the remaining iterations. -/
theorem ensures_while {τ : Tapes} {body : Cmd} {pc i l per exit : ℕ}
    (P : ℕ → Memory → Prop)
    (done : ∀ m, P 0 m → m l ≤ m i ∧ jumpCost l i (pc+body.len+2) m ≤ exit)
    (next : ∀ k m, P (k+1) m → m i < m l ∧
      ∃ v cost, Eval τ body (pc+1) m v cost ∧ P k v ∧
        jumpCost l i (pc+body.len+2) m + cost + jumpCost i i pc v ≤ per)
    {m : Memory} {k : ℕ} (h : P k m) :
    Ensures τ (.whileLT i l body) pc m (k*per+exit) (P 0) := by
  induction k generalizing m with
  | zero =>
    obtain ⟨cmp,le⟩ := done _ h
    exact ⟨m,_,.done cmp,by simpa using le,h⟩
  | succ k ih =>
    obtain ⟨cmp,v,cost,step,inv,le⟩ := next k m h
    obtain ⟨out,t,tail,lt,post⟩ := ih inv
    refine ⟨out,_,.more cmp step tail,?_,post⟩
    rw [Nat.succ_mul]; omega

theorem Ensures.onMachine {τ c pc m budget} {P : Memory → Prop}
    (h : Ensures τ c pc m budget P) {p : Program} (loc : Located p pc (emit c pc))
    (s : State) (hp : s.pc = pc) (hm : s.mem = m) (live : s.halted = false) :
    ∃ t, Reaches p τ s t ∧ t.pc = pc+c.len ∧ P t.mem ∧ t.work ≤ s.work+budget ∧
      t.halted = false ∧ t.out = s.out ∧ t.bot = s.bot := by
  obtain ⟨v,k,ev,hk,hv⟩ := h
  obtain ⟨t,st,tp,tm,tw,tl,to',tb⟩ := ev.sound loc s hp hm live
  exact ⟨t,st,tp,by rw [tm]; exact hv,by rw [tw]; omega,tl,to',tb⟩

/-- Close a structured command by writing a Boolean register and halting. -/
def withOutput (c : Cmd) (reg : ℕ) : Program := c.emit 0 ++ [.output reg, .halt]

/-- End-to-end interface: a high-level semantic/cost certificate supplies a
RunsIn theorem about the emitted RAM. No machine-state reasoning is needed by callers. -/
theorem Ensures.runsIn {τ : Tapes} {c : Cmd} {T reg width : ℕ} {answer : Bool}
    (h : Ensures τ c 0 State.init.mem T
      (fun m => (m reg != 0) = answer ∧ (m reg).size ≤ width)) :
    (c.withOutput reg).RunsIn τ (T + (1+reg.size+width) + 1) (some [answer]) := by
  let p := c.withOutput reg
  have loc : Located p 0 (c.emit 0) := Located.atAppend [] _ _
  obtain ⟨s,reach,pc,⟨ans,bits⟩,time,live,out,bot⟩ :=
    h.onMachine loc State.init rfl rfl rfl
  have ending : Located p s.pc [.output reg,.halt] := by
    rw [pc]; simpa [p,withOutput] using Located.atAppend (c.emit 0) [.output reg,.halt] []
  obtain ⟨z,final,bound,result⟩ := outputHalt live ending reach bot
  exact ⟨z,final,by change s.work ≤ 0+T at time; omega,by simpa [ans,out,State.init] using result⟩

end RamCost.Cmd

/-! Access the actual bit layout of the directed-Hamiltonicity mission. -/
namespace RamCost.Digraph
open TargetedSamplers DirectedHamiltonicity.Main

private theorem flat_get {α β : Type} (rows : List α) (f : α → List β) (n : ℕ)
    (size : ∀ a, (f a).length = n) (r c : ℕ) (hr : r < rows.length) (hc : c < n) :
    (rows.flatMap f)[r*n+c]? = (f rows[r])[c]? := by
  induction rows generalizing r with
  | nil => simp at hr
  | cons a rows ih =>
    cases r with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by rw [size]; exact hc)
    | succ r =>
      have h : r < rows.length := by simpa using hr
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [size, Nat.succ_mul]; omega), size, Nat.succ_mul]
      simpa only [show r*n+n+c-n = r*n+c by omega] using ih r h

theorem adjacency_bit (n : ℕ) (adj : Fin n → Fin n → Bool) (i j : Fin n) :
    (encodeDigraph n adj)[(encNat n).length + i.val*n + j.val]? = some (adj i j) := by
  rw [encodeDigraph, List.getElem?_append_right (by omega)]
  rw [show (encNat n).length + i.val*n + j.val - (encNat n).length = i.val*n+j.val by omega]
  rw [flat_get (List.finRange n) _ n (by simp) _ _ (by simp) j.isLt]
  simp

/-- Register 0 holds the tape address of the start of a row, register 1 the column.
Register 2 is output and scratch. Row starts can be carried in a sequential traversal. -/
def getArc : Block := [.add 2 0 1, .readInput 2 2]

theorem getArc_spec (n : ℕ) (adj : Fin n → Fin n → Bool) (i j : Fin n) (τ : Tapes)
    (m : Memory) (input : τ.input = encodeDigraph n adj)
    (row : m 0 = (encNat n).length + i.val*n) (col : m 1 = j.val) :
    Block.effect τ getArc m = Function.update m 2 (adj i j).toNat ∧
    Block.cost τ getArc m ≤ 12+4*((encNat n).length+n*n).size := by
  have cell : bitVal τ.input[m 0+m 1]? = (adj i j).toNat := by
    rw [input, row, col, adjacency_bit]; rfl
  have rowBound : m 0 + m 1 ≤ (encNat n).length+n*n := by
    have ii := i.isLt
    have jj := j.isLt
    have prod := Nat.mul_le_mul_right n (show i.val+1 ≤ n by omega)
    rw [Nat.succ_mul] at prod
    omega
  have s0 := Nat.size_le_size (show m 0 ≤ (encNat n).length+n*n by omega)
  have s1 := Nat.size_le_size (show m 1 ≤ (encNat n).length+n*n by omega)
  have s2 := Nat.size_le_size rowBound
  have sb : (adj i j).toNat.size ≤ 1 := by cases adj i j <;> decide
  constructor
  · simp [getArc, Block.effect, Op.effect, Op.dest, Op.value, cell]
  · simp [getArc, Block.cost, Op.cost, Op.effect, Op.dest, Op.value, cell]
    change 1+2+0+1+(m 0).size+(m 1).size+(m 0+m 1).size +
      (1+2+2+(m 0+m 1).size+(adj i j).toNat.size) ≤ _
    omega

end RamCost.Digraph

namespace RamCost.Digraph
open TargetedSamplers DirectedHamiltonicity.Main Cmd

private theorem size2 : Nat.size 2 = 2 := rfl
private theorem size3 : Nat.size 3 = 2 := rfl
private theorem size4 : Nat.size 4 = 3 := rfl
attribute [local simp] size2 size3 size4

private def digitStream (bits tail : List Bool) : List Bool :=
  (bits.flatMap fun b => [true,b]) ++ false :: tail

private theorem marker (bs tail : List Bool) (i : ℕ) (h : i ≤ bs.length) :
    (digitStream bs tail)[2*i]? = some (decide (i < bs.length)) := by
  induction bs generalizing i with
  | nil =>
    have : i = 0 := by simpa using h
    subst i; rfl
  | cons b rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa [digitStream, Nat.mul_succ, Nat.succ_lt_succ_iff] using
        ih i (by simpa using h)

theorem header_length (n : ℕ) : (encNat n).length = 2*n.size+1 := by
  simp [encNat, Nat.size_eq_bits_len, Nat.mul_comm]

private theorem tape_marker (pre tail : List Bool) (n i : ℕ) (h : i ≤ n.size) :
    (pre ++ encNat n ++ tail)[pre.length+2*i]? = some (decide (i < n.size)) := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simpa [encNat, digitStream, List.append_assoc, Nat.size_eq_bits_len] using
    marker n.bits tail i (by simpa [Nat.size_eq_bits_len] using h)

private def headerSetup : Block := [.lit 2 0, .lit 3 2, .lit 4 1, .readInput 1 0]
private def headerBody : Block := [.add 0 0 3, .readInput 1 0]
private def headerLoop := Cmd.whileLT 2 1 (.block headerBody)
private def finishHeader : Block := [.add 0 0 4]

/-- Skip one self-delimiting encNat from the given cursor (r0). On exit r0 is the
first bit after the code. The same fragment can skip successive fields. -/
def skipNat := Cmd.seq (.block headerSetup) (.seq headerLoop (.block finishHeader))

private def HeaderInv (start digits k : ℕ) (m : Memory) : Prop :=
  k ≤ digits ∧ m 0 = start+2*(digits-k) ∧ m 1 = (decide (0<k)).toNat ∧
    m 2 = 0 ∧ m 3 = 2 ∧ m 4 = 1

/-- Bound for one header, with both the tape offset and the fragment's code address exposed.
It applies to zero and arbitrary trailing input, with arbitrary initial scratch values. -/
theorem skipNat_spec (τ : Tapes) (pc n : ℕ) (pre tail : List Bool) (m : Memory)
    (tape : τ.input = pre ++ encNat n ++ tail) (cursor : m 0 = pre.length) :
    let width := (pre.length+(encNat n).length).size + (pc+16).size
    Ensures τ skipNat pc m ((n.size+1)*(80+12*width))
      (fun v => v 0 = pre.length+(encNat n).length) := by
  let D := n.size
  let A := (pre.length + (encNat n).length).size
  let P := (pc+16).size
  have read (j : ℕ) (hj : j ≤ D) :
      bitVal τ.input[pre.length+2*j]? = (decide (j < D)).toNat := by
    rw [tape, tape_marker _ _ _ j hj]; rfl
  have aw (j : ℕ) (hj : j ≤ D) : (pre.length+2*j).size ≤ A := by
    apply Nat.size_le_size; rw [header_length]; change _ ≤ pre.length+(2*D+1); omega
  let u := Block.effect τ headerSetup m
  have init : HeaderInv pre.length D D u := by
    have rd := read 0 (by omega)
    simpa [HeaderInv, u, headerSetup, Block.effect, Op.effect, Op.dest, Op.value, cursor]
      using rd
  have startTime : Block.cost τ headerSetup m ≤ 20+A := by
    have rd := read 0 (by omega)
    have b : (bitVal τ.input[pre.length]?).size ≤ 1 := by
      simp only [Nat.mul_zero,Nat.add_zero] at rd; rw [rd]; cases decide (0<D) <;> decide
    have addr : pre.length.size ≤ A := by simpa using aw 0 (by omega)
    simp [headerSetup, Block.cost, Op.cost, Op.effect, Op.dest, Op.value, cursor]
    change (1+2+0) + ((1+2+2) + ((1+3+1) + (1+1+0+pre.length.size+_))) ≤ _
    simpa using (by omega : (1+2+0)+((1+2+2)+((1+3+1)+(1+1+0+pre.length.size+
      (bitVal τ.input[pre.length]?).size))) ≤ 20+A)
  have exit (z : Memory) (h : HeaderInv pre.length D 0 z) :
      z 1 ≤ z 2 ∧ jumpCost 1 2 (pc+4+2+2) z ≤ 10+P := by
    obtain ⟨_,_,flag,zero,_,_⟩ := h
    have w := Nat.size_le_size (show pc+4+2+2 ≤ pc+16 by omega)
    simp [jumpCost,flag,zero]; omega
  have next (k : ℕ) (z : Memory) (h : HeaderInv pre.length D (k+1) z) :
      z 2 < z 1 ∧ ∃ v cost, Eval τ (.block headerBody) (pc+4+1) z v cost ∧
        HeaderInv pre.length D k v ∧
        jumpCost 1 2 (pc+4+2+2) z + cost + jumpCost 2 2 (pc+4) v ≤ 45+6*(A+P) := by
    obtain ⟨hk,addr,flag,zero,two,one⟩ := h
    have kk : D-k = (D-(k+1))+1 := by omega
    have ptr : z 0+2 = pre.length + 2*(D-k) := by rw [addr,kk]; omega
    have rd := read (D-k) (by omega)
    rw [← ptr] at rd
    have test : decide (D-k < D) = decide (0<k) := by
      by_cases pos : 0<k
      · simp [pos, show D-k < D by omega]
      · simp [pos, show ¬ D-k < D by omega]
    rw [test] at rd
    have v0 := aw (D-(k+1)) (by omega)
    have v1 := aw (D-k) (by omega)
    rw [← addr] at v0
    rw [← ptr] at v1
    have bit : (bitVal τ.input[z 0+2]?).size ≤ 1 := by rw [rd]; cases decide (0<k) <;> decide
    have jp := Nat.size_le_size (show pc+4+2+2 ≤ pc+16 by omega)
    have jq := Nat.size_le_size (show pc+4 ≤ pc+16 by omega)
    refine ⟨by simp [flag,zero],_,_,Eval.block ..,?_,?_⟩
    · simp [HeaderInv,headerBody,Block.effect,Op.effect,Op.dest,Op.value,two,zero,one,rd]
      exact ⟨by omega, ptr⟩
    · simp [jumpCost, headerBody, Block.cost, Op.cost, Block.effect, Op.effect, Op.dest, Op.value,
        zero,two,flag]
      omega
  obtain ⟨v,c,ev,le,hv⟩ := ensures_while (HeaderInv pre.length D) exit next init
  obtain ⟨_,ptr,_,_,_,one⟩ := hv
  have ptr' : v 0 = pre.length+2*D := by simpa using ptr
  have last : (v 0+1).size ≤ A := by
    apply Nat.size_le_size; rw [ptr',header_length]; omega
  have before := Nat.size_le_size (Nat.le_add_right (v 0) 1)
  have finishTime : Block.cost τ finishHeader v ≤ 10+2*A := by
    simp [finishHeader,Block.cost, Op.cost,one]; omega
  have final := (Eval.block headerSetup pc m).seq (ev.seq
    (Eval.block finishHeader (pc+4+headerLoop.len) v))
  refine ⟨_,_,final,?_,?_⟩
  · change Block.cost τ headerSetup m + (c+Block.cost τ finishHeader v) ≤ (D+1)*(80+12*(A+P))
    nlinarith
  · simp [finishHeader,Block.effect,Op.effect,Op.dest,Op.value,one,ptr',header_length,D,
      Nat.add_assoc]

end RamCost.Digraph

namespace RamCost
open TargetedSamplers

/-- A conservative register-clobber check. A raw indirect store requires the
more precise memory specification in Array.lean. -/
def Op.Keeps (o : Op) (r : ℕ) : Prop := ∀ m : Memory, r ≠ o.dest m
def Block.Keeps (b : Block) (r : ℕ) : Prop := ∀ o ∈ b, o.Keeps r

/-- Executable clobber test; false is conservative for an indirect store. -/
def Op.keepsReg (o : Op) (r : ℕ) : Bool :=
  match o with
  | .store .. => false
  | other => r != other.dest (fun _ => 0)

theorem Op.keeps_of_check {o : Op} {r : ℕ} (h : o.keepsReg r = true) : o.Keeps r := by
  cases o <;> simp_all [Op.Keeps, Op.keepsReg, Op.dest]

theorem Block.keep {τ : Tapes} {b : Block} {r : ℕ} (h : b.Keeps r) (m : Memory) :
    Block.effect τ b m r = m r := by
  induction b generalizing m with
  | nil => rfl
  | cons o b ih =>
    have t : Block.Keeps b r := fun op hop => h op (List.mem_cons_of_mem _ hop)
    rw [Block.effect, ih t, Op.effect, Function.update_of_ne (h o (by simp) m)]

namespace Cmd

def Keeps : Cmd → ℕ → Prop
  | .block b, r => b.Keeps r
  | .seq c d, r => c.Keeps r ∧ d.Keeps r
  | .ifLE _ _ y n, r => y.Keeps r ∧ n.Keeps r
  | .whileLT _ _ b, r => b.Keeps r

/-- Compute whether an entire command preserves a caller-owned register. -/
def keepsReg : Cmd → ℕ → Bool
  | .block b, r => b.all (fun o => o.keepsReg r)
  | .seq c d, r => c.keepsReg r && d.keepsReg r
  | .ifLE _ _ y n, r => y.keepsReg r && n.keepsReg r
  | .whileLT _ _ b, r => b.keepsReg r

theorem keeps_of_check {c : Cmd} {r : ℕ} (h : keepsReg c r = true) : Keeps c r := by
  induction c with
  | block b =>
    intro o ho; exact Op.keeps_of_check (List.all_eq_true.mp h o ho)
  | seq _ _ a b | ifLE _ _ _ _ a b =>
    exact ⟨a (Bool.and_eq_true_iff.mp h).1, b (Bool.and_eq_true_iff.mp h).2⟩
  | whileLT _ _ _ ih => exact ih h

/-- Certify that every memory write is to a direct register below a cutoff. -/
def writesBelowOp (o : Op) (n : ℕ) : Bool :=
  match o with
  | .store .. => false
  | op => decide (op.dest (fun _ => 0) < n)

def writesBelow : Cmd → ℕ → Bool
  | .block ops, n => ops.all (fun o => writesBelowOp o n)
  | .seq c d, n => c.writesBelow n && d.writesBelow n
  | .ifLE _ _ y z, n => y.writesBelow n && z.writesBelow n
  | .whileLT _ _ b, n => b.writesBelow n

theorem keeps_above {c : Cmd} {n r : ℕ} (check : c.writesBelow n = true) (h : n ≤ r) :
    c.Keeps r := by
  induction c with
  | block ops =>
    intro o ho m
    have atOp : writesBelowOp o n = true := List.all_eq_true.mp check o ho
    cases o with
    | store a b => exact False.elim (Bool.noConfusion atOp)
    | lit d _ | add d _ _ | sub d _ _ | load d _ | inputLength d | readInput d _ | readCoin d _ =>
      change decide (d<n) = true at atOp
      exact (Nat.ne_of_gt ((of_decide_eq_true atOp).trans_le h))
  | seq _ _ a b | ifLE _ _ _ _ a b =>
    exact ⟨a (Bool.and_eq_true_iff.mp check).1,b (Bool.and_eq_true_iff.mp check).2⟩
  | whileLT _ _ _ ih => exact ih check

theorem Eval.keep {τ c pc m v cost} (ev : Eval τ c pc m v cost)
    {r : ℕ} (h : Keeps c r) : v r = m r := by
  induction ev with
  | block ops pc m => exact Block.keep h _
  | seq _ _ first second => exact (second h.2).trans (first h.1)
  | yes _ _ ih => exact ih h.1
  | no _ _ ih => exact ih h.2
  | done _ => rfl
  | more _ _ _ inside next => exact (next h).trans (inside h)

theorem Ensures.frame {τ c pc m budget} {P : Memory → Prop}
    (h : Ensures τ c pc m budget P) :
    Ensures τ c pc m budget (fun v => P v ∧ ∀ r, c.Keeps r → v r = m r) := by
  obtain ⟨v,k,ev,le,post⟩ := h
  exact ⟨v,k,ev,le,post,fun _ hr => ev.keep hr⟩

end Cmd
end RamCost

namespace RamCost
open TargetedSamplers
def Op.Fits (τ : Tapes) (m : Memory) (w : ℕ) : Op → Prop
  | .lit d k => d.size ≤ w ∧ k.size ≤ w
  | .add d a b => d.size ≤ w ∧ a.size ≤ w ∧ b.size ≤ w ∧ (m a).size ≤ w ∧
      (m b).size ≤ w ∧ (m a + m b).size ≤ w
  | .sub d a b => d.size ≤ w ∧ a.size ≤ w ∧ b.size ≤ w ∧ (m a).size ≤ w ∧
      (m b).size ≤ w ∧ (m a - m b).size ≤ w
  | .load d a => d.size ≤ w ∧ a.size ≤ w ∧ (m a).size ≤ w ∧ (m (m a)).size ≤ w
  | .store a b => a.size ≤ w ∧ b.size ≤ w ∧ (m a).size ≤ w ∧ (m b).size ≤ w
  | .inputLength d => d.size ≤ w ∧ τ.input.length.size ≤ w
  | .readInput d a => d.size ≤ w ∧ a.size ≤ w ∧ (m a).size ≤ w ∧ (bitVal τ.input[m a]?).size ≤ w
  | .readCoin d a => d.size ≤ w ∧ a.size ≤ w ∧ (m a).size ≤ w ∧ (bitVal τ.coins[m a]?).size ≤ w

theorem Op.cost_le {o : Op} {τ : Tapes} {m : Memory} {w : ℕ} (h : o.Fits τ m w) :
    o.cost τ m ≤ 1+6*w := by
  cases o <;> simp only [Op.Fits, Op.cost] at * <;> omega

/-- Only widths along the actual abstract execution are required to fit. -/
def Block.Fits (τ : Tapes) (w : ℕ) : Block → Memory → Prop
  | [], _ => True
  | o :: b, m => o.Fits τ m w ∧ Block.Fits τ w b (o.effect τ m)

theorem Block.cost_le {b : Block} {τ : Tapes} {m : Memory} {w : ℕ}
    (h : Block.Fits τ w b m) : Block.cost τ b m ≤ b.length * (1+6*w) := by
  induction b generalizing m with
  | nil => simp [Block.cost]
  | cons o b ih =>
    simpa [Block.cost, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add (Op.cost_le h.1) (ih h.2)


end RamCost

namespace RamCost
open TargetedSamplers

/-- Width obligation for a comparison or an unconditional branch, including
the absolute jump target even when the branch falls through. -/
def JumpFits (w a b target : ℕ) (m : Memory) : Prop :=
  a.size ≤ w ∧ b.size ≤ w ∧ (m a).size ≤ w ∧ (m b).size ≤ w ∧ target.size ≤ w

theorem jumpCost_le {w a b t : ℕ} {m : Memory} (h : JumpFits w a b t m) :
    jumpCost a b t m ≤ 1+6*w := by
  unfold JumpFits at h; unfold jumpCost; omega

namespace Cmd

/-- Unit-cost semantics for the same structured language, indexed by the word
width and total instruction count. A paper proof may work completely in this relation. -/
inductive Words (τ : Tapes) (w : ℕ) : Cmd → ℕ → Memory → Memory → ℕ → Prop
  | block (ops : Block) (pc : ℕ) (m : Memory) : Block.Fits τ w ops m →
    Words τ w (.block ops) pc m (Block.effect τ ops m) ops.length
  | seq {c d pc m u v x y} :
    Words τ w c pc m u x → Words τ w d (pc+c.len) u v y → Words τ w (.seq c d) pc m v (x+y)
  | yes {a b y n pc m v x} : m a ≤ m b → JumpFits w a b (pc+1+n.len+1) m →
    Words τ w y (pc+1+n.len+1) m v x → Words τ w (.ifLE a b y n) pc m v (1+x)
  | no {a b y n pc m v x} : m b < m a → JumpFits w a b (pc+1+n.len+1) m →
    Words τ w n (pc+1) m v x → JumpFits w a a (pc+1+n.len+1+y.len) v →
    Words τ w (.ifLE a b y n) pc m v ((1+x)+1)
  | done {i l body pc m} : m l ≤ m i → JumpFits w l i (pc+body.len+2) m →
    Words τ w (.whileLT i l body) pc m m 1
  | more {i l body pc m u v x y} : m i < m l → JumpFits w l i (pc+body.len+2) m →
    Words τ w body (pc+1) m u x → JumpFits w i i pc u →
    Words τ w (.whileLT i l body) pc u v y →
    Words τ w (.whileLT i l body) pc m v (((1+x)+1)+y)

/-- The paper's charge of one per primitive is sufficient up to a single
explicit bit-width factor for the complete execution, including loop control. -/
theorem Words.refine {τ w c pc m v units} (e : Words τ w c pc m v units) :
    ∃ cost, Eval τ c pc m v cost ∧ cost ≤ units*(1+6*w) := by
  induction e with
  | block b pc m fits => exact ⟨_,.block ..,Block.cost_le fits⟩
  | seq _ _ ha hb =>
    obtain ⟨x,ex,lx⟩ := ha; obtain ⟨y,ey,ly⟩ := hb
    exact ⟨_,.seq ex ey,by rw [Nat.add_mul]; omega⟩
  | yes cmp fit _ ih =>
    obtain ⟨x,ex,lx⟩ := ih
    exact ⟨_,.yes cmp ex,by have := jumpCost_le fit; rw [Nat.add_mul, one_mul]; omega⟩
  | no cmp fit _ back ih =>
    obtain ⟨x,ex,lx⟩ := ih
    have := jumpCost_le fit; have := jumpCost_le back
    exact ⟨_,.no cmp ex,by simp only [Nat.add_mul,one_mul]; omega⟩
  | done cmp fit => exact ⟨_,.done cmp,by simpa using jumpCost_le fit⟩
  | more cmp fit _ back _ ih it =>
    obtain ⟨x,ex,lx⟩ := ih; obtain ⟨y,ey,ly⟩ := it
    have := jumpCost_le fit; have := jumpCost_le back
    exact ⟨_,.more cmp ex ey,by simp only [Nat.add_mul,one_mul]; omega⟩

theorem Words.onMachine {τ w c pc m v units} (e : Words τ w c pc m v units)
    {p : Program} (loc : Located p pc (Cmd.emit c pc)) (s : State)
    (hp : s.pc = pc) (hm : s.mem = m) (live : s.halted = false) :
    ∃ t, Reaches p τ s t ∧ t.pc = pc+c.len ∧ t.mem = v ∧ t.work ≤ s.work+units*(1+6*w) ∧
      t.halted = false ∧ t.out = s.out ∧ t.bot = s.bot := by
  obtain ⟨cost, ev, h⟩ := e.refine
  exact (show Ensures τ c pc m (units*(1+6*w)) (· = v) from
    ⟨v,cost,ev,h,rfl⟩).onMachine loc s hp hm live

end Cmd
end RamCost

namespace RamCost.Digraph
open Cmd TargetedSamplers DirectedHamiltonicity.Main

private def number : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*number bs

private theorem number_bits (n : ℕ) : number n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b k h ih => rw [Nat.bits_append_bit _ _ h, number, ih, Nat.bit_val]; omega

private theorem drop_le (bits : List Bool) (k : ℕ) : number (bits.drop k) ≤ number bits := by
  induction bits generalizing k with
  | nil => simp [number]
  | cons b bs ih =>
    cases k with
    | zero => exact Nat.le_refl _
    | succ k => change number (bs.drop k) ≤ b.toNat+2*number bs; have := ih k; omega

private theorem digit (bits tail : List Bool) (i : ℕ) (hi : i < bits.length) :
    ((bits.flatMap fun b => [true,b]) ++ false :: tail)[2*i+1]? = some bits[i] := by
  induction bits generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa [Nat.mul_succ] using ih i (by simpa using hi)

private def saveStart : Block := [.lit 14 0, .add 13 0 14]
private def prepare : Block := [.lit 14 0, .add 12 0 14, .lit 4 1, .sub 0 0 4, .lit 10 0, .lit 11 0]
private def readDigit : Block :=
  [.sub 0 0 4, .readInput 7 0, .add 10 10 10, .add 10 10 7, .sub 0 0 4, .add 11 11 4]
private def scan := Cmd.whileLT 13 0 (.block readDigit)
private def restoreCursor : Block := [.add 0 12 14]

/-- Decode an encNat at r0. Outputs are the next tape address (r0), the decoded
natural (r10), and its binary width (r11). The zero code consists solely of its terminator. -/
def decodeNat := Cmd.seq (.block saveStart) (.seq skipNat (.seq (.block prepare)
  (.seq scan (.block restoreCursor))))

private def DecodeInv (n start k : ℕ) (m : Memory) : Prop :=
  k ≤ n.size ∧ m 0=start+2*k ∧ m 13=start ∧ m 4=1 ∧ m 14=0 ∧
    m 12=start+(encNat n).length ∧ m 10=number (n.bits.drop k) ∧ m 11=n.size-k

private theorem decodeSizeFour : Nat.size 4 = 3 := rfl
private theorem size7 : Nat.size 7 = 3 := rfl
private theorem size10 : Nat.size 10 = 4 := rfl
private theorem size11 : Nat.size 11 = 4 := rfl
private theorem size12 : Nat.size 12 = 4 := rfl
private theorem size13 : Nat.size 13 = 4 := rfl
private theorem size14 : Nat.size 14 = 4 := rfl
attribute [local simp] decodeSizeFour size7 size10 size11 size12 size13 size14

theorem decodeNat_spec (τ : Tapes) (pc n : ℕ) (pre tail : List Bool) (m : Memory)
    (tape : τ.input = pre ++ encNat n ++ tail) (cursor : m 0 = pre.length) :
    let W := n.size+(pre.length+(encNat n).length).size+(pc+64).size+6
    Ensures τ decodeNat pc m ((n.size+1)*(300+100*W))
      (fun out => out 0=pre.length+(encNat n).length ∧ out 10=n ∧ out 11=n.size) := by
  let A := pre.length+(encNat n).length
  let W := n.size+A.size+(pc+64).size+6
  let s := Block.effect τ saveStart m
  have s0 : s 0=pre.length := by simp [s,saveStart,Block.effect,Op.effect,Op.dest,Op.value,cursor]
  have s13 : s 13=pre.length := by simp [s,saveStart,Block.effect,Op.effect,Op.dest,Op.value,cursor]
  obtain ⟨u,c,skip,sc,addr,frame⟩ := (skipNat_spec τ (pc+2) n pre tail s tape s0).frame
  have origin := (frame 13 (keeps_of_check (by decide))).trans s13
  let v := Block.effect τ prepare u
  have consumed : n.bits.drop n.size = [] := List.drop_eq_nil_of_le (Nat.size_eq_bits_len n).le
  have init : DecodeInv n pre.length n.size v := by
    simp [DecodeInv, v, prepare, Block.effect, Op.effect, Op.dest, Op.value, origin,addr,
      header_length,consumed,number]
  have width (a : ℕ) (h : a ≤ A) : a.size ≤ A.size := Nat.size_le_size h
  have startW := width pre.length (by dsimp [A]; omega)
  have pcW := Nat.size_le_size (show pc+17+6+2 ≤ pc+64 by omega)
  have back := Nat.size_le_size (show pc+17 ≤ pc+64 by omega)
  have done (u : Memory) (h : DecodeInv n pre.length 0 u) :
      u 0 ≤ u 13 ∧ jumpCost 0 13 (pc+17+6+2) u ≤ 1+6*W := by
    obtain ⟨_,addr,org,_⟩ := h
    refine ⟨by omega,jumpCost_le ?_⟩
    simp [JumpFits,W,addr,org]; omega
  have next (k : ℕ) (u : Memory) (h : DecodeInv n pre.length (k+1) u) :
      u 13 < u 0 ∧ ∃ z cost, Eval τ (.block readDigit) (pc+17+1) u z cost ∧
        DecodeInv n pre.length k z ∧
        jumpCost 0 13 (pc+17+6+2) u + cost + jumpCost 13 13 (pc+17) z ≤ 8*(1+6*W) := by
    obtain ⟨hk,ptr,org,one,zero,endPos,acc,count⟩ := h
    have kd : k < n.bits.length := by rw [Nat.size_eq_bits_len]; omega
    let b := n.bits[k]
    have pos : u 0-1 = pre.length+(2*k+1) := by omega
    have rd : bitVal τ.input[u 0-1]? = b.toNat := by
      rw [pos,tape,List.append_assoc,List.getElem?_append_right (by omega)]
      have d := digit n.bits tail k kd
      simpa [encNat,List.append_assoc,b,bitVal] using congrArg bitVal d
    have numeric : number (n.bits.drop k) = b.toNat+2*u 10 := by
      rw [List.drop_eq_getElem_cons kd, number, acc]
    have total := (drop_le n.bits k).trans_eq (number_bits n)
    have total' := (drop_le n.bits (k+1)).trans_eq (number_bits n)
    have ub : u 10+u 10+b.toNat ≤ n := by omega
    have wa : (u 10).size ≤ n.size := Nat.size_le_size (by omega)
    have wd : (u 10+u 10).size ≤ n.size := Nat.size_le_size (by omega)
    have ws := Nat.size_le_size ub
    have wbit : b.toNat.size ≤ 1 := by cases b <;> decide
    have pu : u 0 ≤ A := by dsimp [A]; rw [header_length]; omega
    have wptr := width _ pu
    have wp1 := width (u 0-1) (by omega)
    have wp2 := width (u 0-1-1) (by omega)
    have wn : n.size.size ≤ n.size := Nat.size_le.mpr Nat.lt_two_pow_self
    have wi := Nat.size_le_size (show u 11 ≤ n.size by omega)
    have wi' := Nat.size_le_size (show u 11+1 ≤ n.size by omega)
    let z := Block.effect τ readDigit u
    have fit : Block.Fits τ W readDigit u := by
      simp [readDigit,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,one,rd,W]
      omega
    have run : Eval τ (.block readDigit) (pc+17+1) u z (Block.cost τ readDigit u) := Eval.block .. 
    have j : JumpFits W 0 13 (pc+17+6+2) u := by simp [JumpFits,W,org]; omega
    have z13 : z 13 = pre.length := by simp [z,readDigit,Block.effect,Op.effect,Op.dest,Op.value,org]
    have bj : JumpFits W 13 13 (pc+17) z := by simp [JumpFits,W,z13]; omega
    refine ⟨by omega,z,_,run,?_,?_⟩
    · simp [DecodeInv,z,readDigit,Block.effect,Op.effect,Op.dest,Op.value,one,zero,org,endPos,rd]
      omega
    · have cb := Block.cost_le fit; change _ ≤ 6*(1+6*W) at cb
      have := jumpCost_le j; have := jumpCost_le bj; omega
  obtain ⟨z,d,ev,dt,_,zp,_,_,zero,endPos,acc,count⟩ := ensures_while (DecodeInv n pre.length) done next init
  have whole := (Eval.block saveStart pc m).seq (skip.seq ((Eval.block prepare (pc+11) u).seq
    (ev.seq (Eval.block restoreCursor (pc+17+scan.len) z))))
  refine ⟨_,_,whole,?_,?_⟩
  · have ph := Nat.size_le_size (show pc+2+16 ≤ pc+64 by omega)
    have cs : Block.cost τ saveStart m ≤ 20+2*A.size := by
      simp [saveStart,Block.cost,Op.cost,Op.effect,Op.dest,Op.value,cursor]; omega
    have decrement := width (A-1) (by omega)
    have cp : Block.cost τ prepare u ≤ 50+4*A.size := by
      change u 0 = A at addr
      simp [prepare,Block.cost,Op.cost,Op.effect,Op.dest,Op.value,addr]; omega
    have cr : Block.cost τ restoreCursor z ≤ 15+2*A.size := by
      change z 12=A at endPos
      simp [restoreCursor,Block.cost,Op.cost,zero,endPos]; omega
    have sc' : c ≤ (n.size+1)*(80+12*W) := sc.trans (Nat.mul_le_mul_left _ (by dsimp [W,A]; omega))
    have overhead : Block.cost τ saveStart m + Block.cost τ prepare u + Block.cost τ restoreCursor z ≤
        (n.size+1)*(85+8*W) := by
      calc
        _ ≤ 85+8*W := by dsimp [W]; omega
        _ ≤ (n.size+1)*_ := Nat.le_mul_of_pos_left _ (by omega)
    change Block.cost τ saveStart m + (c+(Block.cost τ prepare u+(d+Block.cost τ restoreCursor z))) ≤
      (n.size+1)*(300+100*W)
    nlinarith only [sc',overhead,dt]
  · simp [restoreCursor,Block.effect,Op.effect,Op.dest,Op.value,zero,endPos,count,acc,number_bits]

end RamCost.Digraph

namespace DirectedHamiltonicity.TargetGuard
open TargetedSamplers Main RamCost RamCost.Cmd RamCost.Digraph

def fields (xs : List ℕ) := xs.flatMap encNat
private def decField : Block := [.sub 14 14 16]
private def oneField := Cmd.seq skipNat (.block decField)
def skipFields := Cmd.whileLT 15 14 oneField

/-- Parsing a specified field count does not read the trailing tape.
The same command works for every list; the list appears only in the specification. -/
theorem skipFields_spec (τ : Tapes) (pc L : ℕ) (tail : List Bool)
    (xs : List ℕ) (pre : List Bool) (m : Memory)
    (tape : τ.input = pre ++ fields xs ++ tail) (bound : pre.length+(fields xs).length ≤ L)
    (cursor : m 0 = pre.length) (count : m 14 = xs.length) (zero : m 15 = 0) (one : m 16 = 1) :
    let W := L.size+(pc+64).size+5
    Ensures τ skipFields pc m ((L+1)*(220+30*W)*(xs.length+1))
      (fun z => z 0 = pre.length+(fields xs).length) := by
  intro W
  have len (ys : List ℕ) : ys.length ≤ (fields ys).length := by
    induction ys with
    | nil => simp [fields]
    | cons x xs ih =>
      change xs.length+1 ≤ (encNat x ++ fields xs).length
      rw [List.length_append,header_length]; omega
  induction xs generalizing pre m with
  | nil =>
    have e : m 14 = 0 := count
    have le : jumpCost 14 15 (pc+oneField.len+2) m ≤ 220+30*W := by
      have j := Nat.size_le_size (show pc+oneField.len+2 ≤ pc+64 by
        have hlen : oneField.len ≤ 60 := by decide
        omega)
      simp [jumpCost,e,zero]
      have : Nat.size 14 = 4 := rfl
      have : Nat.size 15 = 4 := rfl
      dsimp only [W]; omega
    refine ⟨m,_,Eval.done (by omega),?_,?_⟩
    · simpa using le.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos L))
    · simpa [fields] using cursor
  | cons x xs ih =>
    have tape' : τ.input = pre ++ encNat x ++ (fields xs ++ tail) := by simpa [fields,List.append_assoc] using tape
    have len' : pre.length + (encNat x).length + (fields xs).length ≤ L := by
      simpa [fields,List.length_append,Nat.add_assoc] using bound
    have idx := skipNat_spec τ (pc+1) x pre (fields xs ++ tail) m tape' cursor
    obtain ⟨u,t,ev,le,addr,keep⟩ := idx.frame
    have c14 : u 14 = xs.length+1 := (keep 14 (keeps_of_check (by decide))).trans count
    have z15 : u 15 = 0 := (keep 15 (keeps_of_check (by decide))).trans zero
    have o16 : u 16 = 1 := (keep 16 (keeps_of_check (by decide))).trans one
    let v := Block.effect τ decField u
    have v14 : v 14=xs.length := by simp [v,decField,Block.effect,Op.effect,Op.dest,Op.value,c14,o16]
    have v15 : v 15=0 := by simpa [v,decField,Block.effect,Op.effect,Op.dest] using z15
    have v16 : v 16=1 := by simpa [v,decField,Block.effect,Op.effect,Op.dest] using o16
    have v0 : v 0=(pre++encNat x).length := by simpa [v,decField,Block.effect,Op.effect,Op.dest] using addr
    have tp : τ.input = (pre++encNat x) ++ fields xs ++ tail := by simpa [List.append_assoc] using tape'
    obtain ⟨z,q,rest,rt,result⟩ := ih (pre ++ encNat x) v tp (by simpa using len') v0 v14 v15 v16
    have eval : Eval τ oneField (pc+1) m v (t+Block.cost τ decField u) := Eval.seq ev (.block ..)
    have short : xs.length+1 ≤ L := by have h := len (x::xs); simp only [List.length_cons] at h; omega
    have dx : x.size ≤ L := by rw [header_length] at len'; omega
    have cx := Nat.size_le_size short
    have sx := Nat.size_le_size (show xs.length ≤ L by omega)
    have aw := Nat.size_le_size (show pre.length+(encNat x).length ≤ L by omega)
    have pw := Nat.size_le_size (show pc+1+16 ≤ pc+64 by omega)
    have jp := Nat.size_le_size (show pc+oneField.len+2 ≤ pc+64 by
        have hlen : oneField.len ≤ 60 := by decide
        omega)
    have back := Nat.size_le_size (show pc ≤ pc+64 by omega)
    have step : t ≤ (L+1)*(80+12*W) := by
      exact le.trans (Nat.mul_le_mul (by omega) (by dsimp only [W]; omega))
    have fee : Block.cost τ decField u ≤ 24+3*W := by
      simp [decField,Block.cost,Op.cost,c14,o16]; change 1+4+4+5+(xs.length+1).size+1+xs.length.size ≤ _
      dsimp only [W]; omega
    have jf : jumpCost 14 15 (pc+oneField.len+2) m + jumpCost 15 15 pc v ≤ 26+3*W := by
      simp [jumpCost,count,zero,v15]; change 1+4+4+(xs.length+1).size+0+_+(1+4+4+0+0+_) ≤ _
      dsimp only [W]; omega
    refine ⟨z,_,Eval.more (by rw [zero,count]; simp) eval rest,?_,?_⟩
    · change _ ≤ (L+1)*(220+30*W)*((xs.length+1)+1)
      rw [Nat.mul_succ]
      have slack := Nat.le_mul_of_pos_left (50+6*W) (Nat.succ_pos L)
      nlinarith
    · simpa [fields,List.length_append,Nat.add_assoc] using result
end DirectedHamiltonicity.TargetGuard

namespace DirectedHamiltonicity.TargetGuard
open TargetedSamplers Main RamCost RamCost.Cmd Multidigraph

/-- The last integer is allowed to have unbounded length. Inspect just its sign and
the delimiter at the width limit, while distinguishing an end-of-tape sentinel from a bit. -/
def guardOps : Block :=
  [.readInput 3 0, .lit 2 1, .add 4 1 1, .add 4 0 4, .add 4 4 2,
   .readInput 5 4, .sub 6 2 5, .sub 7 5 2, .add 6 6 7, .sub 6 2 6, .add 3 3 6]

private theorem finalWordMarker (bits : List Bool) (K : ℕ) :
    (((bits.flatMap fun b => [true,b]) ++ [false])[K+K]?) =
      if K < bits.length then some true else if K = bits.length then some false else none := by
  induction bits generalizing K with
  | nil => cases K <;> simp
  | cons b bs ih =>
    cases K with
    | zero => simp
    | succ k =>
      rw [show (k+1)+(k+1) = (k+k)+2 by omega]
      change (((bs.flatMap fun b => [true,b]) ++ [false])[k+k]?) = _
      simpa only [List.length_cons, Nat.succ_lt_succ_iff, Nat.add_right_cancel_iff] using ih k

private theorem read_width (pre : List Bool) (B : ℤ) (K : ℕ) :
    bitVal ((pre ++ encInt B)[pre.length+(K+K)+1]?) =
      if K < B.natAbs.size then 1 else if K = B.natAbs.size then 0 else 2 := by
  rw [List.getElem?_append_right (by omega), show pre.length+(K+K)+1-pre.length = (K+K)+1 by omega]
  simp only [encInt, List.getElem?_cons_succ, encNat, finalWordMarker, Nat.size_eq_bits_len]
  split <;> (try split) <;> rfl

set_option maxHeartbeats 1000000 in
/-- An eleven-instruction fragment, with a cost independent of the integer's actual length. -/
theorem guard (pre : List Bool) (B : ℤ) (K pc : ℕ) (τ : Tapes) (m : Memory)
    (tape : τ.input = pre ++ encInt B) (start : m 0 = pre.length) (cap : m 1 = K) :
    Ensures τ (.block guardOps) pc m (11*(1+6*((pre.length+(K+K)+1).size+4)))
      (fun out => (out 3 != 0) = decide (B < 0 ∨ K < B.natAbs.size) ∧ out 3 ≤ 2) := by
  have sign : bitVal τ.input[pre.length]? = (decide (B<0)).toNat := by
    rw [tape, List.getElem?_append_right (by omega), Nat.sub_self]; rfl
  have ext := read_width pre B K
  rw [← tape] at ext
  let W := (pre.length+(K+K)+1).size+4
  have s0 := Nat.size_le_size (show pre.length ≤ pre.length+(K+K)+1 by omega)
  have s1 := Nat.size_le_size (show K ≤ pre.length+(K+K)+1 by omega)
  have s2 := Nat.size_le_size (show K+K ≤ pre.length+(K+K)+1 by omega)
  have s3 := Nat.size_le_size (show pre.length+(K+K) ≤ pre.length+(K+K)+1 by omega)
  have v : bitVal τ.input[pre.length+(K+K)+1]? ≤ 2 := by rw [ext]; split <;> (try split) <;> decide
  let val := bitVal τ.input[pre.length+(K+K)+1]?
  have vt : val ≤ 2 := v
  let sig := (decide (B<0)).toNat
  have st : sig ≤ 1 := Bool.toNat_le _
  have sz (x : ℕ) (h : x ≤ 4) : x.size ≤ W := by
    have hh := Nat.size_le_size h
    change x.size ≤ _ + 4
    have : Nat.size 4 = 3 := rfl
    omega
  have lit (x : ℕ) (h : x ≤ 7) : x.size ≤ W := by
    have hh := Nat.size_le_size h
    change x.size ≤ _ + 4
    have : Nat.size 7 = 3 := rfl
    omega
  have fit : Block.Fits τ W guardOps m := by
    simp [guardOps,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,start,cap,sign]
    dsimp only [sig] at st
    repeat' apply And.intro
    all_goals first
      | exact lit _ (by decide)
      | exact sz _ (by omega)
      | dsimp [W]; omega
  refine ⟨_,_,.block .., Block.cost_le fit, ?_⟩
  simp [guardOps,Block.effect,Op.effect,Op.dest,Op.value,start,cap,sign,ext]
  by_cases lt : K < B.natAbs.size <;> by_cases eq : K = B.natAbs.size <;> by_cases hn : B < 0 <;> simp [lt,eq,hn]

end DirectedHamiltonicity.TargetGuard

namespace DirectedHamiltonicity.TargetGuard
open TargetedSamplers Main RamCost RamCost.Cmd RamCost.Digraph

private def setup : Block := [.add 14 10 10,.add 14 14 10,.lit 15 0,.lit 16 1,.add 14 14 16,.add 14 14 16]
private def widthOp : Block := [.add 1 0 0]
def classify := Cmd.seq skipNat (.seq decodeNat (.seq (.block setup)
    (.seq skipFields (.seq (.block widthOp) (.block guardOps)))))

private theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem setup_spec (τ : Tapes) (pc m L : ℕ) (z : Memory) (e : z 10=m)
    (bound : 3*m+2 ≤ L) :
    Ensures τ (.block setup) pc z (6*(1+6*(L+5))) (fun v =>
      v 0=z 0 ∧ v 14=3*m+2 ∧ v 15=0 ∧ v 16=1) := by
  have : Nat.size 14 = 4 := rfl
  have : Nat.size 10 = 4 := rfl
  have : Nat.size 15 = 4 := rfl
  have : Nat.size 16 = 5 := rfl
  have fit : Block.Fits τ (L+5) setup z := by
    simp [setup,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,e]
    repeat' apply And.intro
    all_goals first
      | exact (size_le_self _).trans (by omega)
      | decide
      | omega
  refine ⟨_,_,.block ..,Block.cost_le fit,?_⟩
  simp [setup,Block.effect,Op.effect,Op.dest,Op.value,e]; omega

set_option maxHeartbeats 1000000 in
/-- The complete parser starts from zero registers. It skips the entire graph using the
arc count, then probes the unbounded final integer at only two positions. -/
theorem classify_runs (n m : ℕ) (xs : List ℕ) (num : xs.length=3*m+2) (B : ℤ) (coins : List Bool) :
    let pre := encNat n ++ encNat m ++ fields xs
    let L := pre.length
    (classify.withOutput 3).RunsIn (runTapes (pre++encInt B) coins)
      (10000*(L+200)^3) (some [decide (B<0 ∨ 2*L<B.natAbs.size)]) := by
  intro pre L
  let τ := runTapes (pre++encInt B) coins
  have ssl (ys : List ℕ) : ys.length ≤ (fields ys).length := by
    induction ys with
    | nil => simp [fields]
    | cons j js ih =>
      change js.length+1 ≤ (encNat j ++ fields js).length
      rw [List.length_append,header_length]; omega
  have lform : L = (encNat n).length+(encNat m).length+(fields xs).length := by simp [L,pre]
  have bm : 3*m+2 ≤ L := by have := ssl xs; omega
  have hn : n.size ≤ L := by rw [header_length] at lform; omega
  have hm : m.size ≤ L := (size_le_self m).trans (by omega)
  let Q := L+200
  let G := 1000*Q^2
  let V := 1000*Q^3
  have Q1 : 1 ≤ Q := by dsimp [Q]; omega
  have VG : G ≤ V := by dsimp [G,V]; nlinarith [Nat.mul_le_mul_right (Q^2) Q1]
  have left : (encNat n).length.size ≤ L := (size_le_self _).trans (by omega)
  have both : ((encNat n).length+(encNat m).length).size ≤ L := (size_le_self _).trans (by omega)
  have g1 := skipNat_spec τ 0 n [] (encNat m ++ fields xs ++ encInt B) State.init.mem
    (by simp [τ,runTapes,pre,List.append_assoc]) rfl
  have g1' : Ensures τ skipNat 0 State.init.mem G (fun u => u 0=(encNat n).length) := by
    apply g1.weaken _ (by simp)
    simp only [List.length_nil, Nat.zero_add]
    change (n.size+1)*(80+12*((encNat n).length.size+5)) ≤ _
    have z := Nat.mul_le_mul (show n.size+1≤Q by dsimp [Q]; omega)
      (show 80+12*((encNat n).length.size+5) ≤ 1000*Q by dsimp [Q]; omega)
    dsimp only [G]; nlinarith
  have g : Ensures τ classify 0 State.init.mem (G+(G+(G+(V+(G+G)))))
      (fun u => (u 3 != 0) = decide (B<0 ∨ 2*L<B.natAbs.size) ∧ (u 3).size ≤ 2) := by
    apply g1'.seq
    intro u hu
    have g2 := decodeNat_spec τ (0+skipNat.len) m (encNat n) (fields xs ++ encInt B) u
      (by simp [τ,runTapes,pre,List.append_assoc]) hu
    have g2' := g2.weaken (b:=G) (by
      change (m.size+1)*(300+100*(m.size+((encNat n).length+(encNat m).length).size+7+6)) ≤ _
      have z := Nat.mul_le_mul (show m.size+1≤Q by dsimp [Q]; omega)
        (show 300+100*(m.size+((encNat n).length+(encNat m).length).size+7+6) ≤ 1000*Q by dsimp [Q]; omega)
      dsimp only [G]; nlinarith) (fun _ h => h)
    apply g2'.seq
    intro z hz
    have g3 := setup_spec τ (0+skipNat.len+decodeNat.len) m L z hz.2.1 bm
    apply (g3.weaken (b:=G) (by dsimp [G,Q]; nlinarith) (fun _ h => h)).seq
    intro t ht
    have g4 := skipFields_spec τ (0+skipNat.len+decodeNat.len+setup.length) L (encInt B)
      xs (encNat n++encNat m) t (by rfl) (by simpa [L,pre])
      (by simpa [ht.1] using hz.1) (by rw [ht.2.1,num]) ht.2.2.1 ht.2.2.2
    have g4' := g4.weaken (b:=V) (by
      change (L+1)*(220+30*(L.size+7+5))*(xs.length+1) ≤ _
      have z1 := Nat.mul_le_mul (show L+1 ≤ Q by dsimp [Q]; omega)
        (show 220+30*(L.size+7+5) ≤ 1000*Q by have := size_le_self L; dsimp [Q]; omega)
      have z2 := Nat.mul_le_mul z1 (show xs.length+1 ≤ Q by dsimp [Q]; omega)
      dsimp only [V]; nlinarith) (fun _ h => h)
    apply g4'.seq
    intro v hv
    have pos : v 0=L := by simpa [L,pre] using hv
    let pc := 0+skipNat.len+decodeNat.len+setup.length+skipFields.len
    have g5 : Ensures τ (.block widthOp) pc v G (fun z => z 0=L ∧ z 1=2*L) := by
      refine ⟨_,_,.block ..,?_,?_⟩
      · simp [widthOp,Block.cost,Op.cost,pos]
        have := size_le_self L; have := size_le_self (L+L)
        dsimp [G,Q]; nlinarith
      · simp [widthOp,Block.effect,Op.effect,Op.dest,Op.value,pos]; omega
    apply g5.seq
    intro z hz
    have g6 := guard pre B (2*L) (pc+widthOp.length) τ z rfl hz.1 hz.2
    apply g6.weaken
    · change 11*(1+6*((L+(2*L+2*L)+1).size+4)) ≤ _
      have := size_le_self (L+(2*L+2*L)+1)
      dsimp [G,Q]; nlinarith
    · intro x hx; exact ⟨hx.1,(size_le_self _).trans hx.2⟩
  obtain ⟨v,hv,clock,res⟩ := g.runsIn
  refine ⟨v,hv,clock.trans ?_,res⟩
  change G+(G+(G+(V+(G+G))))+(1+2+2)+1 ≤ 10000*Q^3
  have : 1 ≤ Q^3 := Nat.one_le_pow _ _ (by omega)
  dsimp [V] at VG ⊢; omega
end DirectedHamiltonicity.TargetGuard

namespace DirectedHamiltonicity.TargetGuard
open TargetedSamplers Main RamCost RamCost.Cmd Multidigraph Finset
theorem path_range {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t : Fin n) (B : ℤ) (out : B < 0 ∨ ((n-1)*W:ℕ) < B) :
    H.weightedPathCount w s t B = 0 := by
  classical
  rw [Multidigraph.weightedPathCount, Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro p _
  have hi : pathWeight w p ≤ (n-1)*W := by
    have su := Finset.sum_le_sum (s:=univ) (fun i _ => hw (p i))
    simpa [pathWeight] using su
  obtain hn | hn := out <;> omega

/-- A width bound on every admissible path weight suffices to reject long integers. -/
theorem range_of_guard {n m W : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t : Fin n) (B : ℤ) (K : ℕ) (width : ((n-1)*W).size ≤ K)
    (hit : B < 0 ∨ K < B.natAbs.size) : H.weightedPathCount w s t B = 0 := by
  apply path_range H w hw s t B
  rcases hit with neg | big
  · exact Or.inl neg
  · by_cases neg : B < 0
    · exact Or.inl neg
    · right
      have gt : (n-1)*W < B.natAbs := by
        by_contra! le
        have := Nat.size_le_size le
        omega
      omega

/-- End-to-end at the target field, with the machine's actual instruction, state, and cost types. -/
theorem guard_on_machine (pre : List Bool) (B : ℤ) (K : ℕ) (τ : Tapes) (s : State)
    (tape : τ.input = pre ++ encInt B) (cursor : s.mem 0 = pre.length) (cap : s.mem 1 = K)
    (sp : s.pc = 0) (live : s.halted = false) :
    let code := guardOps.code
    let out := (code.step τ)^[11] s
    out.pc = 11 ∧ out.halted = false ∧ out.out = s.out ∧ out.bot = s.bot ∧
      out.work ≤ s.work + 11*(1+6*((pre.length+(K+K)+1).size+4)) ∧
      (out.mem 3 != 0) = decide (B < 0 ∨ K < B.natAbs.size) := by
  intro code out
  have localSpec := guard pre B K 0 τ s.mem tape cursor cap
  obtain ⟨v,t,ev,le,ret⟩ := localSpec
  cases ev
  have loc : Located code s.pc guardOps.code := by
    rw [sp]; intro i _; rw [Nat.zero_add]
  have hh := Block.sound guardOps code τ s live loc
  exact ⟨by rw [show out.pc = _ from hh.pc,sp]; rfl,
    hh.live, hh.out, hh.bot, by rw [show out.work = _ from hh.work]; omega,
    by rw [show out.mem = _ from hh.mem]; exact ret.1⟩
end DirectedHamiltonicity.TargetGuard


namespace DirectedHamiltonicity.TargetGuard
open TargetedSamplers Main Main.Multidigraph RamCost.Digraph
private def dataFields {n m : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ) (s t : Fin n) :=
  ((List.finRange m).flatMap fun e => [((tail e).val),(head e).val,w e]) ++ [s.val,t.val]

private theorem fields_length (xs : List ℕ) (T : ℕ) (ht : ∀ x ∈ xs, x ≤ T) :
    (fields xs).length ≤ xs.length*(2*T+1) := by
  induction xs with
  | nil => simp [fields]
  | cons x xs ih =>
    have h1 := ht x (by simp)
    have h2 := ih (fun z hz => ht z (List.mem_cons_of_mem _ hz))
    have hs : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
    change (encNat x ++ fields xs).length ≤ (xs.length+1)*(2*T+1)
    rw [List.length_append,header_length,Nat.add_mul xs.length 1,one_mul]; omega

private theorem width_member (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    x.size ≤ (fields xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    change _ ≤ (encNat y ++ fields ys).length
    rw [List.length_append,header_length]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h; omega
end DirectedHamiltonicity.TargetGuard

open DirectedHamiltonicity.TargetGuard TargetedSamplers DirectedHamiltonicity.Main DirectedHamiltonicity.Main.Multidigraph
open Classical in
theorem solution :
    ∃ P : TargetedSamplers.Program, ∀ (n m W : ℕ) (tail head : Fin m → Fin n) (w : Fin m → ℕ),
      (∀ e, w e ≤ W) → ∀ (s t : Fin n) (B : ℤ) (coins : List Bool),
        let L := (encodeParityInstance n m tail head w s t 0).length - 2
        let flag := decide (B<0 ∨ 2*L < B.natAbs.size)
        L ≤ 21*(n+m+W+1)^2 ∧
        P.RunsIn (runTapes (encodeParityInstance n m tail head w s t B) coins)
          (10000*(L+200)^3) (some [flag]) ∧
        (flag = true → Multidigraph.weightedPathCount
          (⟨tail,head⟩ : Multidigraph (Fin n) (Fin m)) w s t B = 0) ∧
        (flag = false → 0 ≤ B ∧ B.natAbs.size ≤ 2*L) := by
  classical
  refine ⟨classify.withOutput 3,?_⟩
  intro n m W tail head w hw s t B coins L flag
  let xs := dataFields tail head w s t
  let allF := n::m::xs
  let pre := fields allF
  let T := n+m+W+1
  have enc (z : ℤ) : encodeParityInstance n m tail head w s t z = pre++encInt z := by
    simp [pre,allF,xs,dataFields,fields,encodeParityInstance,List.flatMap_append,
      List.flatMap_assoc,List.append_assoc]
  have len : L = pre.length := by
    dsimp only [L]; rw [enc]; simp [encInt,encNat]
  have sx : xs.length = 3*m+2 := by simp [xs,dataFields,Nat.mul_comm]
  have flat : pre = encNat n ++ encNat m ++ fields xs := by simp [pre,allF,fields,List.append_assoc]
  have dom : ∀ x ∈ allF, x ≤ T := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · dsimp [T]; omega
    rcases List.mem_cons.mp hx with rfl | hx
    · dsimp [T]; omega
    change x ∈ _ ++ [s.val,t.val] at hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e,_,he⟩ := List.mem_flatMap.mp hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      have e1 := (tail e).isLt; have e2 := (head e).isLt; have e3 := hw e
      dsimp [T]; rcases he with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      have := s.isLt; have := t.isLt; dsimp [T]; rcases hx with rfl | rfl <;> omega
  refine ⟨?_,?_,?_,?_⟩
  · have lengthBound := fields_length allF T dom
    have count : allF.length ≤ 7*T := by simp only [allF,List.length_cons,sx]; dsimp [T]; omega
    have size : 2*T+1 ≤ 3*T := by dsimp [T]; omega
    have high := lengthBound.trans (Nat.mul_le_mul count size)
    rw [len]; change (fields allF).length ≤ 21*T^2; nlinarith
  · rw [enc]
    unfold flag
    rw [len,flat]
    exact classify_runs n m xs sx B coins
  · intro hit
    have out : B<0 ∨ 2*L < B.natAbs.size := of_decide_eq_true hit
    by_cases neg : B<0
    · exact path_range _ w hw s t B (Or.inl neg)
    have big := out.resolve_left neg
    have hns := width_member allF n (by simp [allF])
    have tw : ∀ e, (w e).size ≤ L := by
      intro e; rw [len]; apply width_member
      change w e ∈ n::m::xs
      apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
      apply List.mem_append_left
      apply List.mem_flatMap.mpr
      exact ⟨e,by simp,by simp⟩
    have nlt : n < 2^L := Nat.size_le.mp (by simpa [len,pre] using hns)
    have wlt (e) : w e < 2^L := Nat.size_le.mp (tw e)
    have prodlt : (n-1)*2^L < 2^(2*L) := by
      rw [two_mul, pow_add]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    have gt : 2^(2*L) ≤ B.natAbs := by
      by_contra! small
      have := Nat.size_le.mpr small
      omega
    apply path_range _ w (fun e => (wlt e).le) s t B (Or.inr ?_)
    omega
  · intro f
    by_cases a : B<0 <;> by_cases b : 2*L < B.natAbs.size <;> simp_all [flag] <;> omega
