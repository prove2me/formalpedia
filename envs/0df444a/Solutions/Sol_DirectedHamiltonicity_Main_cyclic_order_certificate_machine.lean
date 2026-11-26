-- Prove2me | solution 1 for DirectedHamiltonicity.Main.cyclic_order_certificate_machine
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T15:28:25.770127+00:00
-- url     : https://prove2.me/submissions/aacdff95-fefa-428d-b662-4d9e74de658c

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

namespace RamCost.Digraph
open TargetedSamplers DirectedHamiltonicity.Main Cmd

/-- Uniform Boolean program. For a nonempty directed graph, read its (0,0)
adjacency entry straight from the mission's self-delimiting tape. -/
def firstArc := Cmd.seq skipNat (.block [.readInput 1 0])

theorem firstArc_runsIn (n : ℕ) (pos : 0<n) (adj : Fin n → Fin n → Bool) (coins : List Bool) :
    let h := (encNat n).length
    (firstArc.withOutput 1).RunsIn (runTapes (encodeDigraph n adj) coins)
      ((n.size+1)*(80+12*(h.size+5)) + (3+h.size) + 4)
      (some [adj ⟨0,pos⟩ ⟨0,pos⟩]) := by
  let τ := runTapes (encodeDigraph n adj) coins
  let tail := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => adj i j
  have tape : τ.input = [] ++ encNat n ++ tail := by rfl
  have skip := skipNat_spec τ 0 n [] tail State.init.mem tape rfl
  have cell : τ.input[(encNat n).length]? = some (adj ⟨0,pos⟩ ⟨0,pos⟩) := by
    simpa [τ,runTapes] using adjacency_bit n adj ⟨0,pos⟩ ⟨0,pos⟩
  have go : Ensures τ firstArc 0 State.init.mem
      ((n.size+1)*(80+12*((encNat n).length.size+5)) + (3+(encNat n).length.size))
      (fun z => (z 1 != 0) = adj ⟨0,pos⟩ ⟨0,pos⟩ ∧ (z 1).size ≤ 1) := by
    apply Ensures.seq (show Ensures τ skipNat 0 State.init.mem _
      (fun v => v 0 = (encNat n).length) from by simpa [show Nat.size 16 = 5 from rfl] using skip)
    intro u addr
    refine ⟨_,_,Eval.block ..,?_,?_⟩
    · have small : (adj ⟨0,pos⟩ ⟨0,pos⟩).toNat.size ≤ 1 := by cases adj ⟨0,pos⟩ ⟨0,pos⟩ <;> decide
      simp only [Block.cost,Op.cost,addr,cell,bitVal,Nat.add_zero]
      change 2+(encNat n).length.size+(adj ⟨0,pos⟩ ⟨0,pos⟩).toNat.size ≤ _
      omega
    · simp [Block.effect,Op.effect,Op.dest,Op.value,addr,cell,bitVal]
      cases adj ⟨0,pos⟩ ⟨0,pos⟩ <;> decide
  exact go.runsIn

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

namespace RamCost
open TargetedSamplers

/-- An integer stored as the difference of two unbounded natural-number cells. -/
structure IntRegs where
  pos : ℕ
  neg : ℕ
  deriving Repr

def IntRegs.read (r : IntRegs) (m : Memory) : ℤ := (m r.pos : ℤ) - m r.neg

def IntRegs.flip (r : IntRegs) : IntRegs := ⟨r.neg, r.pos⟩

theorem IntRegs.read_flip (r : IntRegs) (m : Memory) : r.flip.read m = -r.read m := by
  simp [IntRegs.read, IntRegs.flip]

/-- These three conditions suffice even when some inputs and outputs alias. -/
structure AddSafe (d a b : IntRegs) : Prop where
  separate : d.pos ≠ d.neg
  left : a.neg ≠ d.pos
  right : b.neg ≠ d.pos

def addInt (d a b : IntRegs) : Block := [.add d.pos a.pos b.pos, .add d.neg a.neg b.neg]
def subInt (d a b : IntRegs) : Block := addInt d a b.flip

theorem addInt_effect (τ : Tapes) (m : Memory) {d a b : IntRegs} (h : AddSafe d a b) :
    Block.effect τ (addInt d a b) m =
      Function.update (Function.update m d.pos (m a.pos+m b.pos)) d.neg (m a.neg+m b.neg) := by
  simp [addInt, Block.effect, Op.effect, Op.dest, Op.value,
    Function.update_of_ne h.left, Function.update_of_ne h.right]

theorem addInt_spec (τ : Tapes) (m : Memory) {d a b : IntRegs} (h : AddSafe d a b) :
    d.read (Block.effect τ (addInt d a b) m) = a.read m + b.read m := by
  rw [addInt_effect _ _ h]
  simp [IntRegs.read, Function.update_of_ne h.separate]
  omega

theorem subInt_spec (τ : Tapes) (m : Memory) {d a b : IntRegs} (h : AddSafe d a b.flip) :
    d.read (Block.effect τ (subInt d a b) m) = a.read m - b.read m := by
  rw [subInt, addInt_spec _ _ h, IntRegs.read_flip, sub_eq_add_neg]

theorem width_add {a b w : ℕ} (ha : a.size ≤ w) (hb : b.size ≤ w) :
    (a+b).size ≤ w+1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]; have := Nat.size_le.mp ha; have := Nat.size_le.mp hb; omega

/-- A bound expressed solely in terms of input widths, including a carry in each sum. -/
theorem addInt_cost_le (τ : Tapes) (m : Memory) {d a b : IntRegs} (h : AddSafe d a b)
    (w : ℕ) (hdp : d.pos.size ≤ w) (hdn : d.neg.size ≤ w)
    (hap : a.pos.size ≤ w) (han : a.neg.size ≤ w) (hbp : b.pos.size ≤ w) (hbn : b.neg.size ≤ w)
    (ap : (m a.pos).size ≤ w) (an' : (m a.neg).size ≤ w)
    (bp : (m b.pos).size ≤ w) (bn : (m b.neg).size ≤ w) :
    Block.cost τ (addInt d a b) m ≤ 4+12*w := by
  simp [addInt, Block.cost, Op.cost, Op.effect, Op.dest, Op.value,
    Function.update_of_ne h.left, Function.update_of_ne h.right]
  have := width_add ap bp; have := width_add an' bn; omega

/-- Normalize into fresh or suitably disjoint outputs. Each component is a truncated subtraction. -/
def normalizeInt (d a : IntRegs) : Block := [.sub d.pos a.pos a.neg, .sub d.neg a.neg a.pos]

theorem normalizeInt_spec (τ : Tapes) (m : Memory) {d a : IntRegs}
    (disj : d.pos ≠ d.neg) (hp : a.pos ≠ d.pos) (hn : a.neg ≠ d.pos) :
    let v := Block.effect τ (normalizeInt d a) m
    d.read v = a.read m ∧ (v d.pos = 0 ∨ v d.neg = 0) ∧
      v d.pos ≤ m a.pos ∧ v d.neg ≤ m a.neg := by
  dsimp only
  simp [normalizeInt, Block.effect, Op.effect, Op.dest, Op.value, IntRegs.read,
    Function.update_of_ne hp, Function.update_of_ne hn, Function.update_of_ne disj]
  omega

end RamCost

/-! Constant code for membership in a packed natural-number word. The RAM has no
bit-test, shift or division primitive. Shift left with wraparound by doubling and
conditionally subtracting the capacity. Bits are numbered from zero at the low end. -/
namespace RamCost.Packed
open TargetedSamplers Cmd

private theorem size2 : Nat.size 2 = 2 := rfl
private theorem size3 : Nat.size 3 = 2 := rfl
private theorem size4 : Nat.size 4 = 3 := rfl
attribute [local simp] size2 size3 size4

private def correction := Cmd.ifLE 1 0 (.block [.sub 0 0 1]) (.block [])
private def doubleWord := Cmd.block [.add 0 0 0]
private def shift := Cmd.seq doubleWord correction
private def decDistance := Cmd.block [.sub 2 2 4]
private def round := Cmd.seq shift decDistance
private def loop := Cmd.whileLT 3 2 round
private def decideHigh := Cmd.ifLE 1 0 (.block [.lit 0 1]) (.block [.lit 0 0])
/-- ABI: r0 word/result, r1 capacity, r2 distance below the most significant
bit, r3 zero, r4 one. All register addresses are independent of word width. -/
def member := Cmd.seq loop (.seq doubleWord decideHigh)

private theorem size_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self)

private theorem doubled_mod {x cap : ℕ} (hx : x < cap) :
    (x+x)%cap = (if cap ≤ x+x then x+x-cap else x+x) := by
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem shift_bit {x top j : ℕ} (hj : j < top) :
    ((x+x) % 2^(top+1)).testBit (j+1) = x.testBit j := by
  rw [show x+x = x*2^1 by omega, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  simp [show j+1 < top+1 by omega]

private theorem shift_eval (τ : Tapes) (pc top : ℕ) (m : Memory)
    (cap : m 1 = 2^(top+1)) (hx : m 0 < m 1) :
    let x := m 0
    let out := Function.update m 0 ((x+x) % m 1)
    ∃ cost, Eval τ shift pc m out cost ∧ cost ≤ 35+8*(top+2)+2*(pc+12).size := by
  let x := m 0
  let u := Function.update m 0 (x+x)
  have first : Eval τ doubleWord pc m u (1+x.size+x.size+(x+x).size) := by
    exact Eval.block _ _ _
  have cs : (m 1).size = top+2 := by rw [cap, Nat.size_pow]
  have sx : x.size ≤ top+1 := Nat.size_le.mpr (cap ▸ hx)
  have sd : (x+x).size ≤ top+2 := width_add sx sx
  have p2 := Nat.size_le_size (show pc+1+1+0+1 ≤ pc+12 by omega)
  have p3 := Nat.size_le_size (show pc+1+1+0+1+1 ≤ pc+12 by omega)
  change (pc+1+1+1).size ≤ (pc+12).size at p2
  change (pc+1+1+1+1).size ≤ (pc+12).size at p3
  change ∃ cost, Eval τ shift pc m (Function.update m 0 ((x+x)%m 1)) cost ∧ _
  rw [doubled_mod hx]
  by_cases h : m 1 ≤ x+x
  · rw [if_pos h]
    have cmp : u 1 ≤ u 0 := by simpa [u] using h
    have last := Eval.yes (τ := τ) (a := 1) (b := 0) (n := .block []) (pc := pc+1)
      cmp (Eval.block [.sub 0 0 1] _ u)
    have ev := first.seq last
    have le := Nat.size_le_size (Nat.sub_le (x+x) (m 1))
    refine ⟨(1+x.size+x.size+(x+x).size) +
        (jumpCost 1 0 (pc+1+1+0+1) u + Block.cost τ [.sub 0 0 1] u), ?_, ?_⟩
    · simpa [shift, doubleWord, correction, Cmd.len, x, u, Block.effect, Op.effect, Op.dest, Op.value]
        using ev
    · simp [jumpCost, Block.cost, Op.cost, u]
      omega
  · rw [if_neg h]
    have cmp : u 0 < u 1 := by simpa [u] using Nat.lt_of_not_ge h
    have last := Eval.no (τ := τ) (a := 1) (b := 0) (y := .block [.sub 0 0 1]) (pc := pc+1)
      cmp (Eval.block [] _ u)
    refine ⟨_, first.seq last, ?_⟩
    change 1+x.size+x.size+(x+x).size +
      ((jumpCost 1 0 (pc+1+1+0+1) u + 0) + jumpCost 1 1 (pc+1+1+0+1+1) u) ≤ _
    simp [jumpCost, u]
    omega

private def Inv (top : ℕ) (bit : Bool) (k : ℕ) (m : Memory) : Prop :=
  m 1 = 2^(top+1) ∧ m 3 = 0 ∧ m 4 = 1 ∧ m 2 = k ∧ m 0 < m 1 ∧
    (m 0).testBit (top-k) = bit ∧ k ≤ top

private theorem loop_spec (τ : Tapes) (pc top k : ℕ) (bit : Bool) (m : Memory)
    (h : Inv top bit k m) :
    Ensures τ loop pc m (k*(100+16*(top+2)+5*(pc+20).size)+(15+3*(pc+20).size))
      (Inv top bit 0) := by
  apply ensures_while (Inv top bit) _ _ h
  · intro u ⟨_,zero,_,dst,_,_,_⟩
    have target := Nat.size_le_size (show pc+round.len+2 ≤ pc+20 by change pc+5+2 ≤ pc+20; omega)
    simp [jumpCost, zero, dst]
    omega
  · intro k u ⟨cap,zero,one,dst,hx,selected,hk⟩
    obtain ⟨c,ev,time⟩ := shift_eval τ (pc+1) top u cap hx
    let x := u 0
    let y := (x+x) % u 1
    let v := Function.update u 0 y
    let z := Function.update v 2 k
    have sub : Eval τ decDistance (pc+1+shift.len) v z
        (1+2+2+3+(k+1).size+1+k.size) := by
      have e := Eval.block (τ := τ) [.sub 2 2 4] (pc+1+shift.len) v
      simpa [decDistance, z, v, Block.effect, Block.cost, Op.effect, Op.cost, Op.dest, Op.value,
        dst, one] using e
    refine ⟨by omega, z, _, .seq ev sub, ?_, ?_⟩
    · have bound : y < u 1 := Nat.mod_lt _ (by rw [cap]; positivity)
      have pos : top-(k+1)<top := by omega
      have bit' : y.testBit (top-k) = bit := by
        change ((u 0+u 0)%u 1).testBit _ = _
        rw [cap, show top-k = (top-(k+1))+1 by omega, shift_bit pos, selected]
      simpa [Inv, z, v, cap, zero, one, bit', y, x] using
        (show y < 2^(top+1) ∧ y.testBit (top-k) = bit ∧ k ≤ top from
          ⟨cap ▸ bound, bit', by omega⟩)
    · have target := Nat.size_le_size (show pc+round.len+2 ≤ pc+20 by change pc+5+2 ≤ pc+20; omega)
      have entry := Nat.size_le_size (show pc ≤ pc+20 by omega)
      have inner := Nat.size_le_size (show pc+1+12 ≤ pc+20 by omega)
      have s1 := size_self (k+1)
      have s0 := size_self k
      change jumpCost 2 3 (pc+round.len+2) u + (c + _) + jumpCost 3 3 pc z ≤ _
      simp [jumpCost, z, v, zero, dst] at *
      omega

private theorem high (top x : ℕ) (hx : x < 2^(top+1)) :
    x.testBit top = decide (2^(top+1) ≤ x+x) := by
  have d : 2^(top+1) = 2^top*2 := pow_succ _ _
  by_cases h : 2^top ≤ x
  · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h hx, decide_eq_true (by omega)]
  · rw [Nat.testBit_lt_two_pow (by omega), decide_eq_false (by omega)]

/-- Constant-size membership kernel, for arbitrary bit widths and input contents.
cap = 2^(top+1); reg 2 holds the distance top-i. The returned word is 0 or 1. -/
theorem member_spec (τ : Tapes) (pc top i : ℕ) (m : Memory)
    (valid : i ≤ top) (cap : m 1 = 2^(top+1)) (hx : m 0 < m 1)
    (distance : m 2 = top-i) (zero : m 3 = 0) (one : m 4 = 1) :
    Ensures τ member pc m
      ((top-i)*(100+16*(top+2)+5*(pc+20).size) + (65+8*(top+2)+7*(pc+20).size))
      (fun v => v 0 = ((m 0).testBit i).toNat) := by
  let bit := (m 0).testBit i
  have initial : Inv top bit (top-i) m :=
    ⟨cap,zero,one,distance,hx,by simp [bit, show top-(top-i)=i by omega],by omega⟩
  obtain ⟨u, c, e, time, hc, _, _, _, hu, hb, _⟩ := loop_spec τ pc top (top-i) bit m initial
  have hbit : (u 0).testBit top = bit := by simpa using hb
  let x := u 0
  let v := Function.update u 0 (x+x)
  have dbl : Eval τ doubleWord (pc+loop.len) u v (1+x.size+x.size+(x+x).size) := Eval.block _ _ _
  have cs : (u 1).size = top+2 := by rw [hc,Nat.size_pow]
  have sx : x.size ≤ top+1 := Nat.size_le.mpr (hc ▸ hu)
  have sd := width_add sx sx
  have p1 := Nat.size_le_size
    (show pc+loop.len+doubleWord.len+1+1+1 ≤ pc+20 by change pc+7+1+1+1+1 ≤ _; omega)
  have p2 := Nat.size_le_size
    (show pc+loop.len+doubleWord.len+1+1+1+1 ≤ pc+20 by change pc+7+1+1+1+1+1 ≤ _; omega)
  have out : decide (u 1 ≤ x+x) = bit := by
    rw [hc]; exact (high top x (hc ▸ hu)).symm.trans hbit
  by_cases h : u 1 ≤ x+x
  · have cmp : v 1 ≤ v 0 := by simpa [v] using h
    have endEv := Eval.yes (τ := τ) (a := 1) (b := 0) (n := .block [.lit 0 0])
      (pc := pc+loop.len+doubleWord.len) cmp (Eval.block [.lit 0 1] _ v)
    refine ⟨_,_,e.seq (dbl.seq endEv),?_,?_⟩
    · change c + (1+x.size+x.size+(x+x).size +
        (jumpCost 1 0 (pc+loop.len+doubleWord.len+1+1+1) v + (1+0+1+0))) ≤ _
      simp [jumpCost, v]
      omega
    · change _ = bit.toNat
      have hb : bit = true := by simpa [h] using out.symm
      rw [hb]; rfl
  · have cmp : v 0 < v 1 := by simpa [v] using Nat.lt_of_not_ge h
    have endEv := Eval.no (τ := τ) (a := 1) (b := 0) (y := .block [.lit 0 1])
      (pc := pc+loop.len+doubleWord.len) cmp (Eval.block [.lit 0 0] _ v)
    refine ⟨_,_,e.seq (dbl.seq endEv),?_,?_⟩
    · change c + (1+x.size+x.size+(x+x).size +
        ((jumpCost 1 0 (pc+loop.len+doubleWord.len+1+1+1) v + (1+0+0+0)) +
        jumpCost 1 1 (pc+loop.len+doubleWord.len+1+1+1+1) (Block.effect τ [.lit 0 0] v))) ≤ _
      simp [jumpCost, v, Block.effect, Op.effect, Op.dest, Op.value]
      omega
    · change _ = bit.toNat
      have hb : bit = false := by simpa [h] using out.symm
      rw [hb]; rfl

end RamCost.Packed

namespace RamCost.Packed
open TargetedSamplers Cmd

private def setupRegs : Block := [.lit 1 1, .lit 3 0, .lit 4 1, .lit 6 0]
private def powerBody : Block := [.add 1 1 1, .add 6 6 4]
private def powerLoop := Cmd.whileLT 6 5 (.block powerBody)
private def adjust : Block := [.add 1 1 1, .sub 2 5 2]

/-- Construct a power of two at run time. r5 supplies its exponent and r1 receives the result. -/
def buildPower := Cmd.seq (.block setupRegs) powerLoop

/-- Standalone calling convention: r0 is the packed word, r2 the bit index, and
r5 the index of the top bit. r0 receives the membership bit. The code computes
the capacity from scratch and is independent of all three inputs. -/
def testBit := Cmd.seq buildPower (.seq (.block adjust) member)

private def PowerInv (x i top k : ℕ) (m : Memory) : Prop :=
  k ≤ top ∧ m 0 = x ∧ m 2 = i ∧ m 5 = top ∧ m 3 = 0 ∧ m 4 = 1 ∧
  m 6 = top-k ∧ m 1 = 2^(top-k)

private theorem highersize2 : Nat.size 2 = 2 := rfl
private theorem highersize3 : Nat.size 3 = 2 := rfl
private theorem highersize4 : Nat.size 4 = 3 := rfl
private theorem size5 : Nat.size 5 = 3 := rfl
private theorem size6 : Nat.size 6 = 3 := rfl
attribute [local simp] highersize2 highersize3 highersize4 size5 size6

theorem buildPower_spec (τ : Tapes) (pc : ℕ) (m : Memory) :
    let top := m 5
    let P := (pc+40).size
    Ensures τ buildPower pc m (15+(top*(60+16*top+2*P)+(12+2*top+P)))
      (fun u => u 0=m 0 ∧ u 2=m 2 ∧ u 5=top ∧ u 3=0 ∧ u 4=1 ∧ u 1=2^top) := by
  let top := m 5
  let x := m 0
  let i := m 2
  let P := (pc+40).size
  have self (j : ℕ) : j.size ≤ j := Nat.size_le.mpr Nat.lt_two_pow_self
  have init : PowerInv x i top top (Block.effect τ setupRegs m) := by
    simp [PowerInv, setupRegs, Block.effect, Op.effect, Op.dest, Op.value, x, i, top]
  have exit (z : Memory) (h : PowerInv x i top 0 z) :
      z 5 ≤ z 6 ∧ jumpCost 5 6 (pc+4+2+2) z ≤ 12+2*top+P := by
    obtain ⟨_,_,_,width,_,_,pos,_⟩ := h
    have tgt := Nat.size_le_size (show pc+4+2+2 ≤ pc+40 by omega)
    have := self top
    simp [jumpCost,width,pos]; omega
  have next (k : ℕ) (z : Memory) (h : PowerInv x i top (k+1) z) :
      z 6 < z 5 ∧ ∃ v cost, Eval τ (.block powerBody) (pc+4+1) z v cost ∧
        PowerInv x i top k v ∧ jumpCost 5 6 (pc+4+2+2) z + cost +
        jumpCost 6 6 (pc+4) v ≤ 60+16*top+2*P := by
    obtain ⟨hk,x0,i2,width,zero,one,pos,pow⟩ := h
    have diff : top-k = (top-(k+1))+1 := by omega
    have doubled : z 1+z 1 = 2^(top-k) := by rw [diff,pow,pow_succ]; omega
    have s1 : (z 1).size ≤ top+1 := by rw [pow, Nat.size_pow]; omega
    have sd : (z 1+z 1).size ≤ top+1 := by rw [doubled, Nat.size_pow]; omega
    have si : (z 6).size ≤ top := (self _).trans (by omega)
    have sj : (z 6+1).size ≤ top := (self _).trans (by omega)
    have sw : (z 5).size ≤ top := width ▸ self top
    have tgt := Nat.size_le_size (show pc+4+2+2 ≤ pc+40 by omega)
    have back := Nat.size_le_size (show pc+4 ≤ pc+40 by omega)
    refine ⟨by omega,_,_,Eval.block ..,?_,?_⟩
    · simp [PowerInv,powerBody,Block.effect,Op.effect,Op.dest,Op.value,x0,i2,width,
        zero,one,doubled,pos]; omega
    · simp [jumpCost, powerBody, Block.cost, Block.effect, Op.cost, Op.effect, Op.dest, Op.value, one]
      omega
  obtain ⟨u,c,ev,time,_,ux,ui,ut,uz,uo,_,up⟩ :=
    ensures_while (PowerInv x i top) exit next init
  exact ⟨_,_,(Eval.block setupRegs pc m).seq ev, Nat.add_le_add_left time 15,
    ux,ui,ut,uz,uo,by simpa using up⟩

theorem testBit_spec (τ : Tapes) (pc : ℕ) (m : Memory)
    (inside : m 2 ≤ m 5) (fits : m 0 < 2^(m 5+1)) :
    let top := m 5
    Ensures τ testBit pc m ((top+1)*(240+45*(top+2+(pc+40).size)))
      (fun v => v 0 = ((m 0).testBit (m 2)).toNat) := by
  let top := m 5
  let x := m 0
  let i := m 2
  let P := (pc+40).size
  have self (j : ℕ) : j.size ≤ j := Nat.size_le.mpr Nat.lt_two_pow_self
  obtain ⟨u,c,ev,time,ux,ui,ut,uz,uo,up⟩ := buildPower_spec τ pc m
  change u 0 = x at ux
  change u 2 = i at ui
  change u 5 = top at ut
  change u 1 = 2^top at up
  change c ≤ 15+(top*(60+16*top+2*P)+(12+2*top+P)) at time
  have cap : u 1+u 1 = 2^(top+1) := by simp [up,pow_succ,Nat.mul_two]
  let z := Block.effect τ adjust u
  have memCap : z 1 = 2^(top+1) := by simp [z,adjust,Block.effect,Op.effect,Op.dest,Op.value,cap]
  have memX : z 0 = x := by simp [z,adjust,Block.effect,Op.effect,Op.dest,Op.value,ux]
  have dist : z 2 = top-i := by simp [z,adjust,Block.effect,Op.effect,Op.dest,Op.value,ut,ui]
  have zero : z 3 = 0 := by simp [z,adjust,Block.effect,Op.effect,Op.dest,Op.value,uz]
  have one : z 4 = 1 := by simp [z,adjust,Block.effect,Op.effect,Op.dest,Op.value,uo]
  obtain ⟨v,d,ge,dt,result⟩ := member_spec τ (pc+4+4+2) top i z inside memCap
    (by rw [memX,memCap]; exact fits) dist zero one
  have run := ev.seq ((Eval.block adjust (pc+4+4) u).seq ge)
  refine ⟨v,_,run,?_,?_⟩
  · have small := self top
    have si := (self i).trans inside
    have ss := (self (top-i)).trans (Nat.sub_le top i)
    have addr := Nat.size_le_size (show pc+4+4+2+20 ≤ pc+40 by omega)
    have adj : Block.cost τ adjust u ≤ 25+6*(top+2) := by
      have sd : (2^top+2^top).size = top+2 := by rw [← Nat.mul_two, ← pow_succ, Nat.size_pow]
      simp [adjust,Block.cost,Op.cost,Op.effect,Op.dest,Op.value,ut,ui,up,Nat.size_pow,sd]
      omega
    change c + (Block.cost τ adjust u + d) ≤ (top+1)*(240+45*(top+2+P))
    have mul := Nat.mul_le_mul (Nat.sub_le top i)
      (show 100+16*(top+2)+5*(pc+4+4+2+20).size ≤ 100+16*(top+2)+5*P by omega)
    nlinarith
  · simpa [memX] using result

end RamCost.Packed

/-! Multiply two unsigned words using the RAM's addition, monus, and branches.
A Horner scan consumes the multiplier from its most significant end. -/
namespace RamCost.Multiply
open TargetedSamplers Cmd

private def clearRegs : Block := [.lit 6 0, .lit 7 0]
private def doubling : Block := [.add 2 2 2, .add 7 7 7, .add 6 6 4]
private def takeBit : Block := [.sub 2 2 1, .add 7 7 0]
private def branch := Cmd.ifLE 1 2 (.block takeBit) (.block [])
private def body := Cmd.seq (.block doubling) branch
private def loop := Cmd.whileLT 6 5 body

/-- r0 and r2 are the factors, r5 gives the word width. r7 receives the product.
The output may occupy twice the input width. -/
def program := Cmd.seq Packed.buildPower (.seq (.block clearRegs) loop)

private def Inv (x y w k : ℕ) (m : Memory) : Prop :=
  k ≤ w ∧ m 0 = x ∧ m 1 = 2^w ∧ m 4 = 1 ∧ m 5 = w ∧ m 6 = w-k ∧ m 2 < 2^w ∧
  ∃ q, q < 2^(w-k) ∧ m 7 = q*x ∧ q*2^w + m 2 = y*2^(w-k)

private theorem size2 : Nat.size 2 = 2 := rfl
private theorem size4 : Nat.size 4 = 3 := rfl
private theorem size5 : Nat.size 5 = 3 := rfl
private theorem size6 : Nat.size 6 = 3 := rfl
private theorem size7 : Nat.size 7 = 3 := rfl
attribute [local simp] size2 size4 size5 size6 size7

private theorem iter (τ : Tapes) (pc x y w k : ℕ) (m : Memory) (hx : x < 2^w)
    (inv : Inv x y w (k+1) m) :
    let W := 2*w+10+(pc+32).size
    ∃ out units, Words τ W body pc m out units ∧ units ≤ 6 ∧ Inv x y w k out := by
  obtain ⟨hk, val, cap, one, width, idx, residue, q, small, acc, eqn⟩ := inv
  let W := 2*w+10+(pc+32).size
  have diff : w-k = (w-(k+1))+1 := by omega
  have qw : q < 2^w := small.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  have prod : m 7 < 2^(w+w) := by rw [acc,pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt qw hx
  have rx : (m 0).size ≤ w := val ▸ Nat.size_le.mpr hx
  have rr : (m 2).size ≤ w := Nat.size_le.mpr residue
  have ar : (m 7).size ≤ w+w := Nat.size_le.mpr prod
  have dr := width_add rr rr
  have da := width_add ar ar
  have a3 : (m 7+m 7+m 0).size ≤ (w+w+1)+1 :=
    width_add da (by omega)
  have w6 : (m 6).size ≤ w := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have inc : (m 6+1).size ≤ w := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have wc : (m 1).size = w+1 := by rw [cap,Nat.size_pow]
  have sub := Nat.size_le_size (Nat.sub_le (m 2+m 2) (m 1))
  let u := Block.effect τ doubling m
  have pre : Words τ W (.block doubling) pc m u 3 := by
    apply Words.block
    simp [doubling,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,one,W]; omega
  have fu : u 0=m 0 ∧ u 1=m 1 ∧ u 2=m 2+m 2 ∧ u 4=1 ∧ u 5=w ∧
      u 6=m 6+1 ∧ u 7=m 7+m 7 := by
    simp [u,doubling,Block.effect,Op.effect,Op.dest,Op.value,one,width]
  obtain ⟨u0,u1,u2,u4,u5,u6,u7⟩ := fu
  have j1 := Nat.size_le_size (show pc+3+1+0+1 ≤ pc+32 by omega)
  have j2 := Nat.size_le_size (show pc+3+1+0+1+2 ≤ pc+32 by omega)
  have jumpFit : JumpFits W 1 2 (pc+3+1+0+1) u := by
    change (pc+3+1+1).size ≤ (pc+32).size at j1
    simp [JumpFits,W,u1,u2]; omega
  by_cases take : u 1 ≤ u 2
  · have fit : Block.Fits τ W takeBit u := by
      simp [takeBit,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,u2,u1,u7,u0,W]; omega
    have e := Words.yes (τ := τ) (n := .block []) (pc := pc+3) take jumpFit
      (Words.block takeBit _ u fit)
    refine ⟨_,_,pre.seq e,by decide,?_⟩
    have ge : 2^w ≤ m 2+m 2 := by simpa [u1,u2,cap] using take
    have can : (m 2+m 2-2^w)+2^w = m 2+m 2 := Nat.sub_add_cancel ge
    refine ⟨by omega,?_,?_,?_,?_,?_,?_,2*q+1,?_,?_,?_⟩
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u0,val]
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u1,cap]
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u4]
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u5]
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u6]; omega
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u2,u1,cap]; omega
    · rw [diff,pow_succ]; omega
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u7,u0,val,acc]; ring
    · simp [takeBit,Block.effect,Op.effect,Op.dest,Op.value,u2,u1,cap,diff,pow_succ]
      nlinarith only [eqn,can]
  · have backFit : JumpFits W 1 1 (pc+3+1+0+1+2) u := by
      change (pc+3+1+1+2).size ≤ (pc+32).size at j2
      simp [JumpFits,W,u1]; omega
    have e := Words.no (τ := τ) (y := .block takeBit) (pc := pc+3)
      (Nat.lt_of_not_ge take) jumpFit (Words.block [] _ u trivial) backFit
    refine ⟨_,_,pre.seq e,by decide,?_⟩
    change Inv x y w k u
    refine ⟨by omega,u0.trans val,u1.trans cap,u4,u5,by omega,?_,2*q,?_,?_,?_⟩
    · simpa [u2,u1,cap] using Nat.lt_of_not_ge take
    · rw [diff,pow_succ]; omega
    · rw [u7,acc]; ring
    · rw [u2,diff,pow_succ]; nlinarith only [eqn]

/-- One program for all widths. Its running time is quadratic in the supplied bit width
at a fixed entry address. All multiplication in the proof describes mathematical values. -/
theorem spec (τ : Tapes) (pc : ℕ) (m : Memory)
    (hx : m 0 < 2^(m 5)) (hy : m 2 < 2^(m 5)) :
    let w := m 5
    Ensures τ program pc m ((w+1)*(1000+200*(w+1+(pc+64).size)))
      (fun u => u 7 = m 0 * m 2) := by
  let w := m 5
  let x := m 0
  let y := m 2
  let W := 2*w+10+(pc+64).size
  obtain ⟨u,c,ep,tp,u0,u2,u5,_,u4,u1⟩ := Packed.buildPower_spec τ pc m
  let v := Block.effect τ clearRegs u
  have init : Inv x y w w v := by
    refine ⟨by omega,?_,?_,?_,?_,?_,?_,0,?_,?_,?_⟩ <;>
      simp_all [v,clearRegs,Block.effect,Op.effect,Op.dest,Op.value,x,y,w]
  have exit (s : Memory) (h : Inv x y w 0 s) :
      s 5 ≤ s 6 ∧ jumpCost 5 6 (pc+10+body.len+2) s ≤ 1+6*W := by
    obtain ⟨_,_,_,_,width,idx,_⟩ := h
    have bits : w.size ≤ w := Nat.size_le.mpr Nat.lt_two_pow_self
    have addr := Nat.size_le_size (show pc+10+body.len+2 ≤ pc+64 by change pc+10+7+2 ≤ _; omega)
    refine ⟨by omega,jumpCost_le ?_⟩
    simp [JumpFits,W,width,idx]; omega
  have next (k : ℕ) (s : Memory) (h : Inv x y w (k+1) s) :
      s 6 < s 5 ∧ ∃ out cost, Eval τ body (pc+10+1) s out cost ∧ Inv x y w k out ∧
        jumpCost 5 6 (pc+10+body.len+2) s + cost + jumpCost 6 6 (pc+10) out ≤ 8*(1+6*W) := by
    obtain ⟨out,k',words,count,post⟩ := iter τ (pc+10+1) x y w k s hx h
    obtain ⟨cost,ev,bound⟩ := words.refine
    obtain ⟨hk,_,_,_,width,idx,_⟩ := h
    have bits : w.size ≤ w := Nat.size_le.mpr Nat.lt_two_pow_self
    have si := Nat.size_le_size (show s 6 ≤ w by omega)
    have so := Nat.size_le_size (show out 6 ≤ w by have e := post.2.2.2.2.2.1; omega)
    have addr := Nat.size_le_size (show pc+10+body.len+2 ≤ pc+64 by change pc+10+7+2 ≤ _; omega)
    have back := Nat.size_le_size (show pc+10 ≤ pc+64 by omega)
    have inner := Nat.size_le_size (show pc+10+1+32 ≤ pc+64 by omega)
    have j : JumpFits W 5 6 (pc+10+body.len+2) s := by simp [JumpFits,W,width]; omega
    have b : JumpFits W 6 6 (pc+10) out := by simp [JumpFits,W]; omega
    have bodyBound := Nat.mul_le_mul count (show 1+6*(2*w+10+(pc+10+1+32).size) ≤ 1+6*W by dsimp [W]; omega)
    refine ⟨by omega,out,cost,ev,post,?_⟩
    have := jumpCost_le j; have := jumpCost_le b; omega
  obtain ⟨out,d,loopEv,ld,_,_,_,_,_,_,rr,q,_,prod,identity⟩ :=
    ensures_while (Inv x y w) exit next init
  have full := ep.seq ((Eval.block clearRegs (pc+8) u).seq loopEv)
  refine ⟨out,_,full,?_,?_⟩
  · change c + (8+d) ≤ (w+1)*(1000+200*(w+1+(pc+64).size))
    have a := Nat.size_le_size (show pc+40 ≤ pc+64 by omega)
    change c ≤ 15+(w*(60+16*w+2*(pc+40).size)+(12+2*w+(pc+40).size)) at tp
    dsimp [W] at ld
    have mul := Nat.mul_le_mul_left w a
    nlinarith
  · have nonzero : 0 < 2^w := by positivity
    have eq := congrArg (fun n : ℕ => n/2^w) identity
    simp only [Nat.sub_zero] at eq
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ nonzero, Nat.div_eq_of_lt rr, Nat.zero_add,
      Nat.mul_div_cancel _ nonzero] at eq
    change out 7 = x*y
    rw [prod,eq,Nat.mul_comm]

end RamCost.Multiply

namespace RamCost.Digraph
open Cmd TargetedSamplers DirectedHamiltonicity.Main

private def arcPrivateStart : Block := [.lit 0 0]
private def arcPrivateArgs : Block := [.lit 13 0, .add 12 0 13, .add 0 8 13, .add 2 10 13, .add 5 11 13]
private def arcPrivateFetch : Block := [.add 7 12 7, .add 7 7 9, .readInput 7 7]

/-- Read an arbitrary adjacency bit. Only the row (r8) and column (r9) are
caller inputs. Decode the order and binary width from the original tape,
multiply the row by the order, add the header and column, and read into r7. -/
def arcQuery := Cmd.seq (.block arcPrivateStart) (.seq decodeNat (.seq (.block arcPrivateArgs)
  (.seq Multiply.program (.block arcPrivateFetch))))

private theorem arcPrivateSize2 : Nat.size 2 = 2 := rfl
private theorem arcPrivateSize5 : Nat.size 5 = 3 := rfl
private theorem arcPrivateSize7 : Nat.size 7 = 3 := rfl
private theorem arcPrivateSize8 : Nat.size 8 = 4 := rfl
private theorem arcPrivateSize9 : Nat.size 9 = 4 := rfl
private theorem arcPrivateSize10 : Nat.size 10 = 4 := rfl
private theorem arcPrivateSize11 : Nat.size 11 = 4 := rfl
private theorem arcPrivateSize12 : Nat.size 12 = 4 := rfl
private theorem arcPrivateSize13 : Nat.size 13 = 4 := rfl
attribute [local simp] arcPrivateSize2 arcPrivateSize5 arcPrivateSize7 arcPrivateSize8 arcPrivateSize9 arcPrivateSize10 arcPrivateSize11 arcPrivateSize12 arcPrivateSize13

theorem arcQuery_spec (n : ℕ) (adj : Fin n → Fin n → Bool) (i j : Fin n) (τ : Tapes)
    (pc : ℕ) (m : Memory) (tape : τ.input = encodeDigraph n adj)
    (row : m 8 = i.val) (col : m 9 = j.val) :
    let L := ((encNat n).length+n*n+n+1).size + n.size + (pc+128).size + 1
    Ensures τ arcQuery pc m ((n.size+1)*(3000+500*L)) (fun u => u 7 = (adj i j).toNat) := by
  let h := (encNat n).length
  let size := (h+n*n+n+1).size
  let P := (pc+128).size
  let s := Block.effect τ arcPrivateStart m
  have bitAt := adjacency_bit n adj i j
  let tail := (List.finRange n).flatMap fun a => (List.finRange n).map fun b => adj a b
  have tape' : τ.input = [] ++ encNat n ++ tail := tape
  obtain ⟨u,c,head,ct,⟨addr,nn,ww⟩,frame⟩ := (decodeNat_spec τ (pc+1) n [] tail s tape'
    (by simp [s,arcPrivateStart,Block.effect,Op.effect,Op.dest,Op.value])).frame
  change u 0 = 0+h at addr
  simp only [Nat.zero_add] at addr
  have saved (r : ℕ) (hr : decodeNat.keepsReg r = true) (nz : r ≠ 0) : u r = m r := by
    rw [frame r (keeps_of_check hr)]
    simp [s,arcPrivateStart,Block.effect,Op.effect,Op.dest,Op.value,Function.update_of_ne nz]
  have rr := (saved 8 (by decide) (by decide)).trans row
  have cc := (saved 9 (by decide) (by decide)).trans col
  let v := Block.effect τ arcPrivateArgs u
  have inputs : v 0=i.val ∧ v 2=n ∧ v 5=n.size ∧ v 9=j.val ∧ v 12=h := by
    simp [v,arcPrivateArgs,Block.effect,Op.effect,Op.dest,Op.value,rr,cc,nn,ww,addr]
  obtain ⟨v0,v2,v5,v9,v12⟩ := inputs
  have fit := Nat.lt_size_self n
  obtain ⟨z,d,mul,dt,prod,keep⟩ := (Multiply.spec τ (pc+27+5) v
    (by rw [v0,v5]; exact i.isLt.trans fit) (by rw [v2,v5]; exact fit)).frame
  have z9 := (keep 9 (keeps_of_check (by decide))).trans v9
  have z12 := (keep 12 (keeps_of_check (by decide))).trans v12
  rw [v0,v2] at prod
  have read : bitVal τ.input[h+i.val*n+j.val]? = (adj i j).toNat := by rw [tape,bitAt]; rfl
  have go := (Eval.block arcPrivateStart pc m).seq (head.seq ((Eval.block arcPrivateArgs (pc+27) u).seq
    (mul.seq (Eval.block arcPrivateFetch (pc+27+5+Multiply.program.len) z))))
  refine ⟨_,_,go,?_,?_⟩
  · have iw := Nat.size_le_size (Nat.le_of_lt i.isLt)
    have jw := Nat.size_le_size (Nat.le_of_lt j.isLt)
    have ns : n.size.size ≤ n.size := Nat.size_le.mpr Nat.lt_two_pow_self
    have hw : h.size ≤ size := Nat.size_le_size (by omega)
    have setup : Block.cost τ arcPrivateArgs u ≤ 75+3*(h.size+3*n.size) := by
      simp [arcPrivateArgs,Block.cost,Op.cost,Op.effect,Op.dest,Op.value,addr,rr,nn,ww]
      omega
    have mulRow := Nat.mul_le_mul_right n (Nat.le_of_lt i.isLt)
    have upto := Nat.mul_le_mul_right n (show i.val+1 ≤ n from i.isLt)
    rw [Nat.succ_mul] at upto
    have jj := j.isLt
    have endW := Nat.size_le_size (show h+i.val*n+j.val ≤ h+n*n+n+1 by omega)
    have rowW := Nat.size_le_size (show h+i.val*n ≤ h+n*n+n+1 by omega)
    have prodW := Nat.size_le_size (show i.val*n ≤ h+n*n+n+1 by omega)
    have bb : (adj i j).toNat.size ≤ 1 := by cases adj i j <;> decide
    have finish : Block.cost τ arcPrivateFetch z ≤ 40+7*size+n.size := by
      simp [arcPrivateFetch,Block.cost,Op.cost,Op.effect,Op.dest,Op.value,z12,z9,prod,read]
      dsimp only [size] at *; omega
    have ph := Nat.size_le_size (show pc+1+64 ≤ pc+128 by omega)
    have pm := Nat.size_le_size (show pc+27+5+64 ≤ pc+128 by omega)
    change c ≤ (n.size+1)*(300+100*(n.size+(0+h).size+(pc+1+64).size+6)) at ct
    rw [Nat.zero_add] at ct
    rw [v5] at dt
    change 1+(c+(Block.cost τ arcPrivateArgs u + (d+Block.cost τ arcPrivateFetch z))) ≤
      (n.size+1)*(3000+500*(size+n.size+P+1))
    have c' : c ≤ (n.size+1)*(300+100*(n.size+size+P+6)) :=
      ct.trans (Nat.mul_le_mul_left _ (by dsimp [P]; omega))
    have d' : d ≤ (n.size+1)*(1000+200*(n.size+1+P)) :=
      dt.trans (Nat.mul_le_mul_left _ (by dsimp [P]; omega))
    have overhead : 1+Block.cost τ arcPrivateArgs u+Block.cost τ arcPrivateFetch z ≤ (n.size+1)*(120+10*size+12*n.size) := by
      calc
        _ ≤ 120+10*size+12*n.size := by omega
        _ ≤ (n.size+1)*_ := Nat.le_mul_of_pos_left _ (by omega)
    calc
      _ ≤ (n.size+1)*(300+100*(n.size+size+P+6)) + (n.size+1)*(1000+200*(n.size+1+P)) +
            (n.size+1)*(120+10*size+12*n.size) := by omega
      _ ≤ _ := by rw [← Nat.mul_add, ← Nat.mul_add]; apply Nat.mul_le_mul_left; omega
  · simp [arcPrivateFetch,Block.effect,Op.effect,Op.dest,Op.value,z9,z12,prod,read]

/-- In terms of vertex-count width alone, random adjacency access has quadratic log-cost
at a fixed entry address. The order, its width, and the row offset are computed on the RAM. -/
theorem arcQuery_width (n : ℕ) (adj : Fin n → Fin n → Bool) (i j : Fin n) (τ : Tapes)
    (pc : ℕ) (m : Memory) (tape : τ.input = encodeDigraph n adj)
    (row : m 8 = i.val) (col : m 9 = j.val) :
    Ensures τ arcQuery pc m ((n.size+1)*(8000+2000*(n.size+(pc+128).size)))
      (fun u => u 7 = (adj i j).toNat) := by
  have h := arcQuery_spec n adj i j τ pc m tape row col
  apply h.weaken _ (fun _ p => p)
  have a : (encNat n).length.size ≤ 2*n.size+1 := by
    rw [header_length]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have sq : (n*n).size ≤ n.size+n.size := by
    apply Nat.size_le.mpr; rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self n) (Nat.lt_size_self n)
  have b := width_add a (show (n*n).size ≤ 2*n.size+1 by omega)
  have c := width_add b (show n.size ≤ (2*n.size+1)+1 by omega)
  have d := width_add c (show (1:ℕ).size ≤ ((2*n.size+1)+1)+1 by
    change 1 ≤ _; omega)
  apply Nat.mul_le_mul_left
  omega

end RamCost.Digraph

namespace DirectedHamiltonicity.CycleWitness
open TargetedSamplers Main RamCost RamCost.Cmd RamCost.Digraph
private abbrev WMem := ℕ → ℕ

/-- A candidate cyclic order has one extra entry for the return to the start; a second
array is a claimed left inverse. Both may be arbitrary, including repeated vertices. -/
structure Input (n : ℕ) where
  order : Fin (n+1) → Fin n
  inverse : Fin n → Fin n
  first : ℕ
  second : ℕ
  firstSafe : 32 ≤ first
  secondSafe : 32 ≤ second

def Input.layout {n} (c : Input n) (m : WMem) : Prop :=
  m 20=c.first ∧ m 21=c.second ∧ m 22=n ∧
  (∀ i, m (c.first+i.val) = (c.order i).val) ∧
  (∀ i, m (c.second+i.val) = (c.inverse i).val)

def Input.edgeOK {n} (c : Input n) (adj : Fin n → Fin n → Bool) (i : Fin n) : Prop :=
  adj (c.order i.castSucc) (c.order i.succ) = true ∧ c.inverse (c.order i.castSucc) = i

def Input.valid {n} (c : Input n) (adj : Fin n → Fin n → Bool) : Prop :=
  c.order 0 = c.order (Fin.last n) ∧ ∀ i, c.edgeOK adj i

private def init : Block :=
  [.lit 16 1,.lit 19 0,.load 24 20,.add 17 20 22,.load 25 17,
   .sub 26 24 25,.sub 23 16 26,.sub 26 25 24,.sub 23 23 26]
private def before : Block :=
  [.add 17 20 19,.load 8 17,.add 17 17 16,.load 9 17,.add 17 21 8,.load 24 17]
private def after : Block :=
  [.sub 26 16 7,.sub 23 23 26,.sub 26 24 19,.sub 23 23 26,
   .sub 26 19 24,.sub 23 23 26,.add 19 19 16]
private def body := Cmd.seq (.block before) (.seq arcQuery (.block after))
def checker := Cmd.seq (.block init) (.whileLT 19 22 body)

private def maxAddr {n} (c : Input n) := 64+c.first+c.second+n+1

private theorem preserve {n} (c : Input n) {cmd : Cmd} {τ pc m v t}
    (h : Eval τ cmd pc m v t) (m0 : c.layout m) (ceiling : cmd.writesBelow 32)
    (a : cmd.Keeps 20) (b : cmd.Keeps 21) (d : cmd.Keeps 22) : c.layout v := by
  obtain ⟨b0,b1,sz,ord,rev⟩ := m0
  refine ⟨(h.keep a).trans b0,(h.keep b).trans b1,(h.keep d).trans sz,?_,?_⟩
  · intro i; exact (h.keep (keeps_above ceiling (by have := c.firstSafe; omega))).trans (ord i)
  · intro i; exact (h.keep (keeps_above ceiling (by have := c.secondSafe; omega))).trans (rev i)

private theorem setup {n} (c : Input n) (τ : Tapes) (m : WMem) (layout : c.layout m) :
    let v := Block.effect τ init m
    v 16=1 ∧ v 19=0 ∧ v 23≤1 ∧ (v 23=1 ↔ c.order 0=c.order (Fin.last n)) ∧
      Block.cost τ init m ≤ 9*(1+6*(maxAddr c).size) := by
  intro v
  have hfirst := c.firstSafe
  have hsecond := c.secondSafe
  obtain ⟨addr,_,sz,ord,_⟩ := layout
  let a := (c.order 0).val
  let b := (c.order (Fin.last n)).val
  have r0 : m c.first = a := by simpa [a] using ord 0
  have rl : m (c.first+n) = b := ord (Fin.last n)
  have simpMem : v 16=1 ∧ v 19=0 ∧ v 23=1-(a-b)-(b-a) := by
    simp (disch := omega) [Function.update_of_ne,v,init,Block.effect,Op.effect,Op.dest,Op.value,addr,sz,r0,rl]
  obtain ⟨x,y,z⟩ := simpMem
  have bit : (1-(a-b)-(b-a)=1) ↔ a=b := by omega
  refine ⟨x,y,by omega,by rw [z,bit]; exact Fin.ext_iff.symm,?_⟩
  have h₁ := (c.order 0).isLt; have h₂ := (c.order (Fin.last n)).isLt
  change a<n at h₁; change b<n at h₂
  have fits : Block.Fits τ (maxAddr c).size init m := by
    simp (disch := omega) [Function.update_of_ne,init,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,addr,sz,r0,rl]
    repeat' apply And.intro
    all_goals first
      | apply Nat.size_le_size; dsimp [maxAddr]; omega
      | change Nat.size 1 ≤ (maxAddr c).size; apply Nat.size_le_size; dsimp [maxAddr]; omega
  exact Block.cost_le fits

private theorem prepare {n} (c : Input n) (τ : Tapes) (i : Fin n) (m : WMem) (layout : c.layout m)
    (idx : m 19=i.val) (one : m 16=1) :
    let v := Block.effect τ before m
    v 8 = (c.order i.castSucc).val ∧ v 9 = (c.order i.succ).val ∧
    v 24=(c.inverse (c.order i.castSucc)).val ∧
    Block.cost τ before m ≤ 6*(1+6*(maxAddr c).size) := by
  intro v
  have hfirst := c.firstSafe
  have hsecond := c.secondSafe
  obtain ⟨a,b,_,order,inverse⟩ := layout
  let u := c.order i.castSucc
  let z := c.order i.succ
  have r : m (c.first+i.val)=u.val := order i.castSucc
  have nx : m (c.first+i.val+1)=z.val := by simpa [Nat.add_assoc,z] using order i.succ
  have rv := inverse u
  have effects : v 8=u.val ∧ v 9=z.val ∧ v 24=(c.inverse u).val := by
    simp (disch := omega) [Function.update_of_ne,v,before,Block.effect,Op.effect,Op.dest,Op.value,a,b,idx,one,r,nx,rv]
  refine ⟨effects.1,effects.2.1,effects.2.2,?_⟩
  have fits : Block.Fits τ (maxAddr c).size before m := by
    simp (disch := omega) [Function.update_of_ne,before,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,a,b,idx,one,r,nx,rv]
    repeat' apply And.intro
    all_goals first
      | apply Nat.size_le_size; dsimp [maxAddr]; have := i.isLt; have := u.isLt;
        have := z.isLt; have := (c.inverse u).isLt; omega
      | change Nat.size 1 ≤ (maxAddr c).size; apply Nat.size_le_size; dsimp [maxAddr]; omega
  exact Block.cost_le fits

private theorem finish {n} (c : Input n) (adj : Fin n → Fin n → Bool) (i : Fin n) (τ : Tapes)
    (m : WMem) (idx : m 19=i.val) (one : m 16=1) (bit : m 23≤1)
    (arc : m 7 = (adj (c.order i.castSucc) (c.order i.succ)).toNat)
    (back : m 24 = (c.inverse (c.order i.castSucc)).val) :
    let v := Block.effect τ after m
    v 19=i.val+1 ∧ v 23≤1 ∧ (v 23=1 ↔ m 23=1 ∧ c.edgeOK adj i) ∧
    Block.cost τ after m ≤ 7*(1+6*(maxAddr c).size) := by
  intro v
  let a := adj (c.order i.castSucc) (c.order i.succ)
  let j := c.inverse (c.order i.castSucc)
  have da : m 7=a.toNat := arc
  have dj : m 24=j.val := back
  have data : v 19=i.val+1 ∧ v 23=m 23-(1-a.toNat)-(j.val-i.val)-(i.val-j.val) := by
    simp [v,after,Block.effect,Op.effect,Op.dest,Op.value,idx,one,da,dj]
  refine ⟨data.1,by rw [data.2]; omega,?_,?_⟩
  · rw [data.2]
    change _ ↔ _ ∧ a=true ∧ j=i
    by_cases eq : j=i
    · subst j; cases a <;> simp_all
    · have ij : j.val≠i.val := fun h => eq (Fin.ext h)
      cases a <;> simp [eq] <;> omega
  · have al : a.toNat≤1 := Bool.toNat_le _
    have fits : Block.Fits τ (maxAddr c).size after m := by
      simp [after,Block.Fits,Op.Fits,Op.effect,Op.dest,Op.value,idx,one,da,dj]
      repeat' apply And.intro
      all_goals first
        | apply Nat.size_le_size; dsimp [maxAddr]; have := i.isLt; have := j.isLt; omega
        | change Nat.size 1 ≤ (maxAddr c).size; apply Nat.size_le_size; dsimp [maxAddr]; omega
    exact Block.cost_le fits

theorem Input.sound {n} (c : Input n) (adj : Fin n → Fin n → Bool) (good : c.valid adj) :
    HasHamCycle n adj := by
  cases n with
  | zero => exact (c.order 0).elim0
  | succ n =>
    let f (i : Fin (n+1)) := c.order i.castSucc
    have left : Function.LeftInverse c.inverse f := fun i => (good.2 i).2
    let σ := Equiv.ofBijective f ⟨left.injective,Finite.injective_iff_surjective.mp left.injective⟩
    refine ⟨Nat.succ_pos _,σ,?_⟩
    intro i
    change adj (f i) (f (finRotate (n+1) i)) = true
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [finRotate_last]
      have h := (good.2 (Fin.last n)).1
      simpa [f,Fin.succ_last,← good.1] using h
    · have rot : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [rot]
      exact (good.2 j.castSucc).1

private def Invariant {n} (c : Input n) (adj : Fin n → Fin n → Bool) (i : ℕ) (m : WMem) : Prop :=
  c.layout m ∧ m 16=1 ∧ m 19=i ∧ m 23≤1 ∧
  (m 23=1 ↔ c.order 0=c.order (Fin.last n) ∧ ∀ j : Fin n, j.val < i → c.edgeOK adj j)

private theorem iteration {n} (c : Input n) (adj : Fin n → Fin n → Bool) (i : Fin n)
    (τ : Tapes) (pc : ℕ) (m : WMem) (tape : τ.input = encodeDigraph n adj)
    (inv : Invariant c adj i.val m) :
    ∃ v t, Eval τ body pc m v t ∧ Invariant c adj (i.val+1) v ∧
      t ≤ 13*(1+6*(maxAddr c).size) + (n.size+1)*(8000+2000*(n.size+(pc+before.length+128).size)) := by
  obtain ⟨layout,one,idx,bit,good⟩ := inv
  let u := Block.effect τ before m
  have p := prepare c τ i m layout idx one
  have pre : Eval τ (.block before) pc m u (Block.cost τ before m) := .block ..
  obtain ⟨z,x,ev,clock,arc,keep⟩ := (arcQuery_width n adj (c.order i.castSucc)
    (c.order i.succ) τ (pc+before.length) u tape p.1 p.2.1).frame
  have mid := Eval.seq pre ev
  have iz : z 19=i.val := (mid.keep (keeps_of_check (by decide))).trans idx
  have oz : z 16=1 := (mid.keep (keeps_of_check (by decide))).trans one
  have bz : z 23=m 23 := mid.keep (keeps_of_check (by decide))
  have jz : z 24=(c.inverse (c.order i.castSucc)).val :=
    (keep 24 (keeps_of_check (by decide))).trans p.2.2.1
  have post := finish c adj i τ z iz oz (bz ▸ bit) arc jz
  let v := Block.effect τ after z
  have final : Eval τ (.block after) (pc+before.length+arcQuery.len) z v (Block.cost τ after z) :=
    .block ..
  have run : Eval τ body pc m v (Block.cost τ before m+(x+Block.cost τ after z)) := .seq pre (.seq ev final)
  have lay := preserve c run layout (by decide) (keeps_of_check (by decide))
    (keeps_of_check (by decide)) (keeps_of_check (by decide))
  refine ⟨v,_,run,⟨lay,(run.keep (keeps_of_check (by decide))).trans one,post.1,post.2.1,?_⟩,?_⟩
  · rw [post.2.2.1,bz,good]
    constructor
    · rintro ⟨⟨closed,prev⟩,here⟩
      refine ⟨closed,?_⟩
      intro j hj
      by_cases eq : j=i
      · simpa [eq] using here
      · have : j.val≠i.val := fun h => eq (Fin.ext h)
        exact prev j (by omega)
    · rintro ⟨cl,allE⟩
      exact ⟨⟨cl,fun j hj => allE j (by omega)⟩,allE i (by omega)⟩
  · have hb := p.2.2.2; have ha := post.2.2.2; omega


/-- A fixed checker for a proposed ordering. It reads both arrays and the official graph
tape, scans every cyclic edge, and checks the candidate inverse at every position. -/
theorem check {n} (c : Input n) (adj : Fin n → Fin n → Bool) (τ : Tapes)
    (pc : ℕ) (m : WMem) (tap : τ.input = encodeDigraph n adj) (lay : c.layout m) :
    let W := (maxAddr c).size
    let J := (pc+512).size
    let Q := 300*(1+W+J)+(n.size+1)*(8000+2000*(n.size+J))
    Ensures τ checker pc m ((n+2)*Q) (fun out => out 23 ≤ 1 ∧ (out 23=1 ↔ c.valid adj)) := by
  classical
  intro W J Q
  let u := Block.effect τ init m
  let entry := pc+init.length
  let A := 9*(1+6*W)
  have ready := setup c τ m lay
  have ev : Eval τ (.block init) pc m u (Block.cost τ init m) := .block ..
  have layout := preserve c ev lay (by decide) (keeps_of_check (by decide))
    (keeps_of_check (by decide)) (keeps_of_check (by decide))
  have inv : Invariant c adj 0 u := by
    refine ⟨layout,ready.1,ready.2.1,ready.2.2.1,?_⟩
    simpa using ready.2.2.2.1
  let P (k : ℕ) (v : WMem) := k≤n ∧ Invariant c adj (n-k) v
  have nh : n.size ≤ W := Nat.size_le_size (by dsimp [maxAddr]; omega)
  have jmp := Nat.size_le_size (show entry+body.len+2 ≤ pc+512 by
    have : body.len≤300 := by decide
    dsimp [entry]; change pc+9+body.len+2 ≤ pc+512; omega)
  have back := Nat.size_le_size (show entry≤pc+512 by dsimp [entry]; change pc+9 ≤ pc+512; omega)
  have dest := Nat.size_le_size (show entry+1+before.length+128 ≤ pc+512 by
    dsimp [entry]; change pc+9+1+6+128 ≤ pc+512; omega)
  have done : ∀ v, P 0 v → v 22 ≤ v 19 ∧ jumpCost 22 19 (entry+body.len+2) v ≤ Q := by
    intro v ⟨_,q⟩
    obtain ⟨layout,_,idx,_,_⟩ := q
    have size := layout.2.2.1
    simp only [Nat.sub_zero] at idx
    refine ⟨by omega,?_⟩
    simp only [jumpCost,size,idx]
    change 1+5+5+n.size+n.size+_ ≤ _
    dsimp only [Q]
    change _ ≤ J at jmp
    omega
  have next : ∀ k v, P (k+1) v → v 19<v 22 ∧
      ∃ z t, Eval τ body (entry+1) v z t ∧ P k z ∧
        jumpCost 22 19 (entry+body.len+2) v+t+jumpCost 19 19 entry z ≤ Q := by
    intro k v ⟨hk,q⟩
    let i : Fin n := ⟨n-(k+1),by omega⟩
    obtain ⟨z,t,bodyRun,fresh,bound⟩ := iteration c adj i τ (entry+1) v tap q
    have len := q.1.2.2.1
    have idx := q.2.2.1
    have afterIdx := fresh.2.2.1
    have nextIndex : i.val+1=n-k := by dsimp [i]; omega
    have wi := (Nat.size_le_size i.isLt.le).trans nh
    have wnext := (Nat.size_le_size (show i.val+1≤n from i.isLt)).trans nh
    change v 19=i.val at idx
    refine ⟨by have := i.isLt; omega,z,t,bodyRun,⟨by omega,nextIndex ▸ fresh⟩,?_⟩
    simp only [jumpCost,len,idx,afterIdx]
    change 1+5+5+n.size+i.val.size+_+t+(1+5+5+(i.val+1).size+(i.val+1).size+_) ≤ _
    change _ ≤ J at jmp back dest
    have shift := Nat.mul_le_mul_left (n.size+1) (show
        8000+2000*(n.size+(entry+1+before.length+128).size) ≤ 8000+2000*(n.size+J) by omega)
    change t ≤ 13*(1+6*W) + _ at bound
    dsimp only [Q]; omega
  obtain ⟨v,t,loopEval,clock,_,last⟩ :=
    ensures_while (τ:=τ) (pc:=entry) P done next (show P n u from ⟨le_rfl,by simpa using inv⟩)
  refine ⟨v,_,Eval.seq ev loopEval,?_,last.2.2.2.1,?_⟩
  · have hA := ready.2.2.2.2
    change Block.cost τ init m ≤ A at hA
    have aq : A≤Q := by dsimp [A,Q]; omega
    rw [Nat.add_mul]; omega
  · simpa [Input.valid] using last.2.2.2.2

/-- The emitted RAM accepts only actual Hamiltonian digraphs, for every candidate and
claimed inverse; the code is independent of n, the candidate, and the graph. -/
theorem onMachine {n} (c : Input n) (adj : Fin n → Fin n → Bool) (τ : Tapes) (pc : ℕ)
    (p : TargetedSamplers.Program) (loc : Located p pc (checker.emit pc)) (s : State)
    (sp : s.pc=pc) (live : s.halted=false) (tape : τ.input=encodeDigraph n adj)
    (lay : c.layout s.mem) :
    ∃ z, Reaches p τ s z ∧ z.pc=pc+checker.len ∧ z.halted=false ∧
      z.out=s.out ∧ z.bot=s.bot ∧ (z.mem 23 = 1 ↔ c.valid adj) ∧
      (z.mem 23 = 1 → HasHamCycle n adj) ∧
      z.work ≤ s.work+(n+2)*(300*(1+(maxAddr c).size+(pc+512).size)+
        (n.size+1)*(8000+2000*(n.size+(pc+512).size))) := by
  obtain ⟨z,r,ep,⟨_,iff⟩,le,l,out,b⟩ := (check c adj τ pc s.mem tape lay).onMachine loc s sp rfl live
  exact ⟨z,r,ep,l,out,b,iff,fun h => c.sound adj (iff.mp h),le⟩


theorem certificates_iff (n : ℕ) (adj : Fin n → Fin n → Bool) :
    HasHamCycle n adj ↔ ∃ c : Input n, c.valid adj := by
  constructor
  · rintro ⟨pos,σ,edges⟩
    cases n with
    | zero => omega
    | succ n =>
      let xs : Fin ((n+1)+1) → Fin (n+1) := Fin.snoc (fun i => σ i) (σ 0)
      let c : Input (n+1) := ⟨xs,σ.symm,32,32+(n+1)+1,by decide,by omega⟩
      refine ⟨c,?_,?_⟩
      · change xs (0 : Fin (n+2))=xs (Fin.last (n+1))
        change xs (0 : Fin (n+1)).castSucc = _
        simp [xs]
      · intro i
        refine ⟨?_,?_⟩
        · change adj (xs i.castSucc) (xs i.succ) = true
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa [xs,Fin.succ_last,finRotate_last] using edges (Fin.last n)
          · have r : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
            have h := edges j.castSucc
            rw [r] at h
            change adj (xs j.castSucc.castSucc) (xs j.succ.castSucc)=true
            simpa only [xs, Fin.snoc_castSucc] using h
        · change σ.symm (xs i.castSucc)=i; simp [xs]
  · rintro ⟨c,ok⟩; exact c.sound adj ok

end DirectedHamiltonicity.CycleWitness

namespace DirectedHamiltonicity.CycleWitness
open TargetedSamplers Main RamCost
end DirectedHamiltonicity.CycleWitness

open DirectedHamiltonicity.CycleWitness TargetedSamplers DirectedHamiltonicity.Main
open Classical in
theorem solution :
    ∃ P : Program, ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      let valid := fun (q : Fin (n+1) → Fin n) (inv : Fin n → Fin n) =>
        q 0 = q (Fin.last n) ∧ ∀ i : Fin n, adj (q i.castSucc) (q i.succ) = true ∧ inv (q i.castSucc) = i
      (HasHamCycle n adj ↔ ∃ q inv, valid q inv) ∧
      ∀ q inv (τ : Tapes) (s : State), τ.input=encodeDigraph n adj → s.pc=0 → s.halted=false →
        s.mem 20=32 → s.mem 21=33+n → s.mem 22=n →
        (∀ i : Fin (n+1), s.mem (32+i.val) = (q i).val) →
        (∀ i : Fin n, s.mem (33+n+i.val) = (inv i).val) →
        ∃ k z, (P.step τ)^[k] s=z ∧ z.pc=P.length ∧ z.halted=false ∧
          z.out=s.out ∧ z.bot=s.bot ∧ (z.mem 23=1 ↔ valid q inv) ∧
          (z.mem 23=1 → HasHamCycle n adj) ∧ z.work ≤ s.work +
            (n+2)*(300*(11+(130+2*n).size)+(n.size+1)*(8000+2000*(n.size+10))) := by
  refine ⟨checker.emit 0,?_⟩
  intro n adj valid
  constructor
  · rw [certificates_iff]
    constructor
    · rintro ⟨c,h⟩; exact ⟨c.order,c.inverse,h⟩
    · rintro ⟨q,inv,h⟩; exact ⟨⟨q,inv,32,33+n,le_rfl,by omega⟩,h⟩
  · intro q inv τ s tape sp live r20 r21 r22 ord rev
    let c : Input n := ⟨q,inv,32,33+n,le_rfl,by omega⟩
    have loc : RamCost.Located (checker.emit 0) 0 (checker.emit 0) := by intro i _; simp
    obtain ⟨z,⟨k,run⟩,pc,h,o,b,iff,sound,cost⟩ :=
      onMachine c adj τ 0 (checker.emit 0) loc s sp live tape ⟨r20,r21,r22,ord,rev⟩
    refine ⟨k,z,run,by simpa using pc,h,o,b,iff,sound,?_⟩
    have w : 64+c.first+c.second+n+1=130+2*n := by dsimp [c]; omega
    have ten : (0+512:ℕ).size=10 := by decide
    change z.work ≤ s.work + (n+2)*(300*(1+(64+c.first+c.second+n+1).size+(0+512:ℕ).size)+_) at cost
    rw [w,ten] at cost
    simpa only [show ∀ t : ℕ, 1+t+10=11+t by omega] using cost
