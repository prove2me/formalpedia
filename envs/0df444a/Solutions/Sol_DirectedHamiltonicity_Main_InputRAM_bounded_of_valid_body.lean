-- Prove2me | solution 1 for DirectedHamiltonicity.Main.InputRAM.bounded_of_valid_body
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:32:19.48085+00:00
-- url     : https://prove2.me/submissions/5df36189-3dc9-4114-83c5-ac0025713f14

import Theorems.Thm_DirectedHamiltonicity_Main_InputRAM_preprocess_exec

set_option autoImplicit false

section LogCostWordBounds

/-! Bit-cost bounds for bounded-width executions on the published log-cost RAM. -/

namespace TargetedSamplers

/-- The cell indices, jump labels, and literal numbers in an instruction fit in `b` bits. -/
def Instr.fieldsFit (b : ℕ) : Instr → Prop
  | .const x y | .load x y | .store x y | .readInput x y | .readCoin x y =>
      x.size ≤ b ∧ y.size ≤ b
  | .add x y z | .monus x y z | .jle x y z | .query x y z =>
      x.size ≤ b ∧ y.size ≤ b ∧ z.size ≤ b
  | .inputLength x | .readWitness x | .output x => x.size ≤ b
  | .outputBot | .halt => True

/-- Ordinary RAM operations. An instruction reading the full tape length must also pay for it. -/
def Instr.allowedAtWidth (τ : Tapes) (b : ℕ) : Instr → Prop
  | .query .. => False
  | .inputLength _ => τ.input.length.size ≤ b
  | _ => True

theorem size_add_le_succ {u v b : ℕ} (hu : u.size ≤ b) (hv : v.size ≤ b) :
    (u + v).size ≤ b + 1 := by
  rw [Nat.size_le] at *
  rw [pow_succ]
  omega

private theorem bitVal_size_le (u : Option Bool) : (bitVal u).size ≤ 2 := by
  cases u with
  | none => decide
  | some x => cases x <;> decide

/-- A single arithmetic, memory, tape or control instruction on bounded-width data.
The extra bit covers the carry of an addition. Width two also covers the end-of-tape symbol. -/
theorem Program.step_work_le_of_width (P : Program) (τ : Tapes) (st : State) {b : ℕ}
    (hb : 2 ≤ b) (hm : ∀ a, (st.mem a).size ≤ b)
    (hi : ∀ i, P[st.pc]? = some i → i.fieldsFit b ∧ i.allowedAtWidth τ b) :
    (P.step τ st).work ≤ st.work + (6 * b + 2) := by
  by_cases hh : st.halted = true
  · simp [Program.step, hh]
  cases he : P[st.pc]? with
  | none => simp [Program.step, hh, he]
  | some i =>
    obtain ⟨hf, ha⟩ := hi i he
    cases i with
    | const d c => simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | add d a c =>
        have h₁ := hm a; have h₂ := hm c
        have hv := size_add_le_succ h₁ h₂
        simp only [Instr.fieldsFit] at hf
        simp [Program.step, hh, he]
        omega
    | monus d a c =>
        have h₁ := hm a; have h₂ := hm c
        have hv := (Nat.size_le_size (Nat.sub_le (st.mem a) (st.mem c))).trans h₁
        simp only [Instr.fieldsFit] at hf
        simp [Program.step, hh, he]
        omega
    | load d a =>
        have h₁ := hm a; have h₂ := hm (st.mem a)
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | store a c =>
        have h₁ := hm a; have h₂ := hm c
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | jle a c target =>
        have h₁ := hm a; have h₂ := hm c
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | inputLength d =>
        simp only [Instr.fieldsFit] at hf
        change τ.input.length.size ≤ b at ha
        simp [Program.step, hh, he]; omega
    | readInput d a =>
        have h₁ := hm a; have h₂ := bitVal_size_le τ.input[st.mem a]?
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | readCoin d a =>
        have h₁ := hm a; have h₂ := bitVal_size_le τ.coins[st.mem a]?
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | readWitness d =>
        have h₂ := bitVal_size_le τ.witness[st.wcursor]?
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | query d a c => exact False.elim ha
    | output a =>
        have h₁ := hm a
        simp only [Instr.fieldsFit] at hf; simp [Program.step, hh, he]; omega
    | outputBot | halt => simp [Program.step, hh, he]

/-- A halted configuration is the final configuration, also when the supplied step count
padded the execution beyond its first halt. -/
theorem Program.final_eq_of_config_halted (P : Program) (τ : Tapes) (k : ℕ)
    (hh : (P.config τ k).halted = true) : P.final τ = some (P.config τ k) := by
  classical
  let h : ∃ j, (P.config τ j).halted = true := ⟨k, hh⟩
  have hmin := Nat.find_min' h hh
  have hhalt := Nat.find_spec h
  have hfix : P.step τ (P.config τ (Nat.find h)) = P.config τ (Nat.find h) := by
    simp [Program.step, hhalt]
  have hsame : P.config τ (k - Nat.find h + Nat.find h) = P.config τ (Nat.find h) := by
    exact (Function.iterate_add_apply ..).trans (Function.iterate_fixed hfix _)
  rw [Nat.sub_add_cancel hmin] at hsame
  rw [Program.final, dif_pos h, hsame]

/-- Upgrade a number of primitive steps to the actual log-cost of a halting run.
The input and coin strings can be arbitrarily long. Only a length instruction reads their size
(the primitive length instruction acts on the input tape). -/
theorem Program.runsIn_of_bounded_width (P : Program) (τ : Tapes) (steps b : ℕ)
    (hb : 2 ≤ b)
    (hmem : ∀ k < steps, ∀ a, ((P.config τ k).mem a).size ≤ b)
    (hcode : ∀ k < steps, ∀ i, P[(P.config τ k).pc]? = some i →
      i.fieldsFit b ∧ i.allowedAtWidth τ b)
    (hh : (P.config τ steps).halted = true) :
    P.RunsIn τ (steps * (6 * b + 2)) (P.config τ steps).result := by
  refine ⟨_, P.final_eq_of_config_halted τ _ hh, ?_, rfl⟩
  have h (k : ℕ) (hk : k ≤ steps) : (P.config τ k).work ≤ k * (6 * b + 2) := by
    induction k with
    | zero => simp [Program.config, State.init]
    | succ k ih =>
        have hlt : k < steps := by omega
        have hs := P.step_work_le_of_width τ (P.config τ k) hb (hmem k hlt) (hcode k hlt)
        change ((P.step τ)^[(k + 1)] State.init).work ≤ _
        rw [Function.iterate_succ_apply', Nat.succ_mul]
        exact hs.trans (Nat.add_le_add_right (ih hlt.le) _)
  exact h steps le_rfl

end TargetedSamplers

end LogCostWordBounds

section StructuredLogCostRAM

/-! Structured, relocatable programs for the Prove2Me log-cost machine. All costs count
the primitive steps of the published instruction list, including jumps. -/

namespace TargetedSamplers.Structured

@[simp] theorem Cmd.compile_length (c : Cmd) (pc : ℕ) : (c.compile pc).length = c.len := by
  induction c generalizing pc <;> simp_all [compile, len] <;> omega

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

theorem Exec.weakenInv {τ c s t k} {I J : Store → Prop} (h : Exec τ I c s t k)
    (incl : ∀ v, I v → J v) : Exec τ J c s t k := by
  induction h with
  | skip s => exact .skip s
  | op s p h => exact .op s p (incl _ h)
  | seq _ _ first rest => exact first.seq rest
  | yes h _ ih => exact .yes h ih
  | no h _ ih => exact .no h ih
  | done h => exact .done h
  | again h _ _ body rest => exact .again h body rest

/-- A block may be embedded between arbitrary instructions. All internal jump labels are absolute. -/
def Contains (P : Program) (pc : ℕ) (code : Program) : Prop :=
  ∃ pre post : Program, pre.length = pc ∧ P = pre ++ code ++ post

theorem Contains.left {P pc x y} (h : Contains P pc (x++y)) : Contains P pc x := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  exact ⟨pre, y++post, hpc, by simpa [List.append_assoc] using hP⟩

theorem Contains.right {P pc x y} (h : Contains P pc (x++y)) : Contains P (pc+x.length) y := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  exact ⟨pre++x, post, by simp [hpc], by simpa [List.append_assoc] using hP⟩

theorem Contains.one {P pc i} (h : Contains P pc [i]) : P[pc]? = some i := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  rw [hP, ← hpc, List.append_assoc, List.getElem?_append_right (by omega)]
  simp

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

private theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

private theorem step_jle {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (a b dst : ℕ) (hp : P[pc]? = some (.jle a b dst)) :
    Located (P.step τ st) (if s.mem a ≤ s.mem b then dst else pc+1) s := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  constructor <;> simp [Program.step, hc, hh, hb, hm, ho, hp]

private theorem step_jump {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (dst : ℕ) (hp : P[pc]? = some (jump dst)) : Located (P.step τ st) dst s := by
  simpa using step_jle τ h 0 0 dst hp

/-- Every source state of a path satisfies the invariant. -/
inductive Path (P : Program) (τ : Tapes) (ok : State → Prop) : State → State → ℕ → Prop
  | refl (s) : Path P τ ok s s 0
  | step {s t k} : ok s → Path P τ ok (P.step τ s) t k → Path P τ ok s t (k+1)

theorem Path.one {P τ ok s} (h : ok s) : Path P τ ok s (P.step τ s) 1 := .step h (.refl _)

theorem Path.trans {P τ ok s m t k j} (p : Path P τ ok s m k) (q : Path P τ ok m t j) :
    Path P τ ok s t (k+j) := by
  induction p with
  | refl => simpa using q
  | step hs _ ih => simpa [Nat.succ_add] using Path.step hs (ih q)

theorem Path.iterate {P τ ok s t k} (p : Path P τ ok s t k) :
    (P.step τ)^[k] s = t ∧ ∀ j < k, ok ((P.step τ)^[j] s) := by
  induction p with
  | refl s => simp
  | @step s t k hs _ ih =>
    refine ⟨?_, ?_⟩
    · simpa [Function.iterate_succ_apply] using ih.1
    · intro j hj
      cases j with
      | zero => simpa using hs
      | succ j => simpa [Function.iterate_succ_apply] using ih.2 j (by omega)

private def project (st : State) : Store := ⟨st.mem, st.out⟩

private theorem Located.project_eq {st pc s} (h : Located st pc s) : project st = s := by
  cases s
  simp [project, h.memory, h.output]

private theorem branch_sites {P pc a b y n} (h : Contains P pc ((Cmd.branch a b y n).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+n.len+1)) ∧ Contains P (pc+1) (n.compile (pc+1)) ∧
    P[pc+1+n.len]? = some (jump (pc+1+n.len+1+y.len)) ∧
    Contains P (pc+1+n.len+1) (y.compile (pc+1+n.len+1)) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.left.one, by simpa using h.right.right.right⟩

private theorem loop_sites {P pc a b body} (h : Contains P pc ((Cmd.whileGt a b body).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+body.len+1)) ∧ Contains P (pc+1) (body.compile (pc+1)) ∧
    P[pc+1+body.len]? = some (jump pc) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.one⟩

/-- Compilation preserves the result, every primitive step count, and the asserted store invariant. -/
theorem Exec.compile_correct {τ inv c s t k} (ev : Exec τ inv c s t k) (P : Program)
    (pc : ℕ) (st : State) (hc : Contains P pc (c.compile pc)) (hp : Located st pc s) (hi : inv s) :
    ∃ t', Path P τ (fun st => inv (project st)) st t' k ∧ Located t' (pc+c.len) t := by
  induction ev generalizing pc st with
  | skip s => exact ⟨st, .refl _, hp⟩
  | op s p _ => exact ⟨_, .one (hp.project_eq ▸ hi), step_op τ hp p hc.one⟩
  | @seq x y s m t u v ex _ ix iy =>
    obtain ⟨mid,p,hm⟩ := ix pc st hc.left hp hi
    obtain ⟨out,q,ho⟩ := iy (pc+x.len) mid (by simpa using hc.right) hm (ex.post hi)
    exact ⟨out, p.trans q, by simpa [Cmd.len, Nat.add_assoc] using ho⟩
  | @yes a b y n s t k h _ iy =>
    obtain ⟨ht,_,_,hy⟩ := branch_sites hc
    have hj := step_jle τ hp a b _ ht
    rw [if_pos h] at hj
    obtain ⟨out,p,ho⟩ := iy _ _ hy hj hi
    exact ⟨out, (Path.one (hp.project_eq ▸ hi)).trans p, by simpa [Cmd.len, Nat.add_assoc] using ho⟩
  | @no a b y n s t k h en ino =>
    obtain ⟨ht,hn,hj,_⟩ := branch_sites hc
    have hs := step_jle τ hp a b _ ht
    rw [if_neg h] at hs
    obtain ⟨mid,p,hm⟩ := ino _ _ hn hs hi
    have hJump := step_jump τ hm _ hj
    exact ⟨_, ((Path.one (hp.project_eq ▸ hi)).trans p).trans (.one (hm.project_eq ▸ en.post hi)),
      by simpa [Cmd.len, Nat.add_assoc] using hJump⟩
  | @done a b body s h =>
    have hj := step_jle τ hp a b _ (loop_sites hc).1
    rw [if_pos h] at hj
    exact ⟨_, .one (hp.project_eq ▸ hi), by simpa [Cmd.len, Nat.add_assoc] using hj⟩
  | @again a b body s m t k j h eb _ ib il =>
    obtain ⟨ht,hbody,hback⟩ := loop_sites hc
    have hs := step_jle τ hp a b _ ht
    rw [if_neg h] at hs
    obtain ⟨mid,p,hm⟩ := ib _ _ hbody hs hi
    have hret := step_jump τ hm pc hback
    obtain ⟨out,q,ho⟩ := il pc _ hc hret (eb.post hi)
    exact ⟨out, (((Path.one (hp.project_eq ▸ hi)).trans p).trans (.one (hm.project_eq ▸ eb.post hi))).trans q, ho⟩

end TargetedSamplers.Structured

end StructuredLogCostRAM

section StructuredLogCostRun

namespace TargetedSamplers.Structured

/-- Maximum bit length of the numerical fields of an instruction. -/
def fieldWidth : Instr → ℕ
  | .const a b | .load a b | .store a b | .readInput a b | .readCoin a b => max a.size b.size
  | .add a b c | .monus a b c | .jle a b c | .query a b c => max a.size (max b.size c.size)
  | .output a | .inputLength a | .readWitness a => a.size
  | .outputBot | .halt => 0

theorem fieldsFit_iff (i : Instr) (w : ℕ) : i.fieldsFit w ↔ fieldWidth i ≤ w := by
  cases i <;> simp [Instr.fieldsFit, fieldWidth]

/-- Static width is a constant for a fixed finite program. -/
def staticWidth : Program → ℕ
  | [] => 2
  | i :: p => max (fieldWidth i) (staticWidth p)

theorem staticWidth_ge_two (P : Program) : 2 ≤ staticWidth P := by
  induction P with
  | nil => rfl
  | cons i p ih => exact ih.trans (le_max_right ..)

theorem fieldsFit_static {P : Program} {i : Instr} (h : i ∈ P) : i.fieldsFit (staticWidth P) := by
  rw [fieldsFit_iff]
  induction P with
  | nil => cases h
  | cons a p ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left .. 
    · exact (ih h).trans (le_max_right ..)

private theorem op_allowed (a : Op) (τ : Tapes) (w : ℕ) : a.instruction.allowedAtWidth τ w := by
  cases a <;> trivial

private theorem compile_allowed (c : Cmd) (pc : ℕ) (τ : Tapes) (w : ℕ) :
    ∀ i ∈ c.compile pc, i.allowedAtWidth τ w := by
  induction c generalizing pc with
  | skip => simp [Cmd.compile]
  | op p => simpa [Cmd.compile] using op_allowed p τ w
  | seq a b ha hb =>
    intro i hi
    exact (List.mem_append.mp hi).elim (ha pc i) (hb (pc+a.len) i)
  | branch a b y n hy hn =>
    intro i hi
    simp only [Cmd.compile, List.mem_append, List.mem_singleton] at hi
    rcases hi with rfl | hi | rfl | hi
    · trivial
    · exact hn _ _ hi
    · trivial
    · exact hy _ _ hi
  | whileGt a b body ih =>
    intro i hi
    simp only [Cmd.compile, List.mem_append, List.mem_singleton] at hi
    rcases hi with rfl | hi | rfl
    · trivial
    · exact ih _ _ hi
    · trivial

def initial : Store := ⟨fun _ => 0, []⟩

/-- A store-level derivation for a full structured program yields its actual published RAM
run and bit cost. A single extra primitive instruction halts after the block returns. -/
theorem Exec.runsIn {τ : Tapes} {c : Cmd} {t : Store} {k width : ℕ}
    (ev : Exec τ (fun s => s.Fits width) c initial t k) :
    let b := max width (staticWidth c.program)
    c.program.RunsIn τ ((k+1)*(6*b+2)) (some t.out) := by
  let P := c.program
  let b := max width (staticWidth P)
  have hinit : initial.Fits width := by intro a; simp [initial]
  have hloc : Located State.init 0 initial := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have hc : Contains P 0 (c.compile 0) := ⟨[],[.halt],rfl,rfl⟩
  obtain ⟨last,path,loc⟩ := ev.compile_correct P 0 State.init hc hloc hinit
  have he : P.config τ k = last := path.iterate.1
  have hpc : last.pc = (c.compile 0).length := by simpa using loc.counter
  have hhalt : P[last.pc]? = some .halt := by simp [hpc, P, Cmd.program]
  have hend : P.config τ (k+1) = {last with halted := true, work := last.work+1} := by
    change (P.step τ)^[k+1] State.init = _
    rw [Function.iterate_succ_apply']
    change P.step τ (P.config τ k) = _
    simp [he, Program.step, loc.live, hhalt]
  have hfit (i : Instr) (hi : i ∈ P) : i.fieldsFit b ∧ i.allowedAtWidth τ b := by
    constructor
    · exact (fieldsFit_iff ..).2 (((fieldsFit_iff ..).1 (fieldsFit_static hi)).trans (le_max_right ..))
    · rcases List.mem_append.mp hi with hm | hm
      · exact compile_allowed c 0 τ b i hm
      · simp at hm
        subst i
        trivial
  have hm (j : ℕ) (hj : j < k+1) (a : ℕ) : ((P.config τ j).mem a).size ≤ b := by
    by_cases h : j < k
    · exact (path.iterate.2 j h a).trans (le_max_left ..)
    · have hj' : j = k := by omega
      rw [hj', he, loc.memory]
      exact ((ev.post hinit) a).trans (le_max_left ..)
  have run := P.runsIn_of_bounded_width τ (k+1) b ((staticWidth_ge_two P).trans (le_max_right ..)) hm
    (fun j _ i hi => hfit i (List.mem_of_getElem? hi)) (by rw [hend])
  simpa [hend, State.result, loc.normal, loc.output] using run

end TargetedSamplers.Structured

end StructuredLogCostRun

section StructuredLogCostFragments

namespace TargetedSamplers.Structured

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)

end TargetedSamplers.Structured

end StructuredLogCostFragments

section LogCostRAMRanges

namespace TargetedSamplers.Structured

/-- An ascending loop can charge each iteration separately. A cumulative cost
bound permits output-sensitive enumeration even when one trial returns many words. -/
theorem forRange_exec_budget {τ : Tapes} {b : ℕ} (ptr stop one lo count : ℕ) (budget : ℕ → ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ budget i+k+3 ≤ budget (i+1) ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      budget 0+j ≤ budget count+1 ∧ state count t := by
  have run (left i : ℕ) (he : i+left = count) (u : Store) (hi : state i u) (hf : u.Fits b) :
      ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) u t j ∧
        budget i+j ≤ budget count+1 ∧ state count t := by
    induction left generalizing i u with
    | zero =>
      have eq : i = count := by omega
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      exact ⟨u,1,.done (by rw [hs,hp,eq]),by rw [eq],eq ▸ hi⟩
    | succ left ih =>
      obtain ⟨hp,hs⟩ := control i (by omega) u hi
      obtain ⟨v,k,ex,hk,hp',h1,hn⟩ := bodyRun i (by omega) u hi hf
      have hnext : (Op.add ptr ptr one).eval τ v = v.write ptr (lo+i+1) := by simp [Op.eval,hp',h1]
      have hiw := (Nat.size_le_size (show lo+i+1 ≤ lo+count by omega)).trans width
      have inc : Exec τ (fun st => st.Fits b) (.op (.add ptr ptr one)) v (v.write ptr (lo+i+1)) 1 := by
        simpa only [hnext] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) v (.add ptr ptr one)
          (by rw [hnext]; exact Store.write_fits (ex.post hf) ptr hiw))
      obtain ⟨t,j,loop,hj,ret⟩ := ih (i+1) (by omega) _ hn (inc.post (ex.post hf))
      refine ⟨t,_,.again (by rw [hs,hp]; omega) (ex.seq inc) loop,?_,ret⟩
      omega
  exact run count 0 (by simp) s start fit

/-- A constant bound on the loop body gives three further primitive instructions
per iteration for the comparison, increment and back edge. -/
theorem forRange_exec {τ : Tapes} {b : ℕ} (ptr stop one lo count bound : ℕ) (body : Cmd)
    (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr = lo+i ∧ s.mem stop = lo+count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ bound ∧ u.mem ptr = lo+i ∧ u.mem one = 1 ∧
        state (i+1) (u.write ptr (lo+i+1)))
    (width : (lo+count).size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(bound+3)+1 ∧ state count t := by
  obtain ⟨t,j,run,cost,final⟩ := forRange_exec_budget (τ := τ) ptr stop one lo count
    (fun i => i*(bound+3)) body state control (fun i hi u hu fu => by
      obtain ⟨v,k,ex,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      exact ⟨v,k,ex,by rw [Nat.succ_mul]; omega,ptr,unit,next⟩) width s start fit
  exact ⟨t,j,run,by simpa using cost,final⟩

/-- The outer loop pays once per trial and once per returned word. The result keeps
both counts separate so that a cap on their total gives a linear trial budget. -/
theorem forRange_exec_reported {τ : Tapes} {b : ℕ} (ptr stop one count setup perWord : ℕ)
    (reports : ℕ → ℕ) (body : Cmd) (state : ℕ → Store → Prop)
    (control : ∀ i ≤ count, ∀ s, state i s → s.mem ptr=i ∧ s.mem stop=count)
    (bodyRun : ∀ i < count, ∀ s, state i s → s.Fits b →
      ∃ u k, Exec τ (fun st => st.Fits b) body s u k ∧ k ≤ setup+reports i*perWord ∧
        u.mem ptr=i ∧ u.mem one=1 ∧ state (i+1) (u.write ptr (i+1)))
    (width : count.size ≤ b) (s : Store) (start : state 0 s) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (forRange ptr stop one body) s t j ∧
      j ≤ count*(setup+3)+prefixReports reports count*perWord+1 ∧ state count t := by
  let budget := fun i => i*(setup+3)+prefixReports reports i*perWord
  obtain ⟨t,j,ex,cost,post⟩ := forRange_exec_budget (τ := τ) ptr stop one 0 count budget body state
    (by simpa only [Nat.zero_add] using control) (fun i hi u hu fu => by
      obtain ⟨v,k,run,work,ptr,unit,next⟩ := bodyRun i hi u hu fu
      refine ⟨v,k,run,?_,by simpa using ptr,unit,by simpa using next⟩
      simp only [budget,prefixReports,Nat.succ_mul,Nat.add_mul]
      omega) (by simpa using width) s start fit
  exact ⟨t,j,ex,by simpa [budget,prefixReports] using cost,post⟩

end TargetedSamplers.Structured

end LogCostRAMRanges

section BoundedBinaryInput

/-! A bounded reader for little-endian self-delimiting naturals. Each payload bit is
preceded by a one; a zero marker terminates the field. -/

namespace BoundedBinaryInput

private def payload (bs : List Bool) : List Bool := bs.flatMap fun b => [true, b]

private theorem read_payload (k : ℕ) (bs rest : List Bool) :
    read k (payload bs ++ false :: rest) =
      if bs.length ≤ k then some (bs.foldr Nat.bit 0) else none := by
  induction bs generalizing k with
  | nil => cases k <;> rfl
  | cons b bs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change (read k (payload bs ++ false :: rest)).map (Nat.bit b) = _
      rw [ih]
      by_cases h : bs.length ≤ k <;> simp [h]

theorem fold_bits (x : ℕ) : x.bits.foldr Nat.bit 0 = x := by
  induction x using Nat.binaryRec' with
  | zero => rfl
  | bit b x h ih => simp [Nat.bits_append_bit x b h, ih]

/-- Returns the original value if it fits, and rejects an oversized numeral independently
of its uninspected high digits or the contents of the following fields. -/
theorem read_encoded (k x : ℕ) (rest : List Bool) :
    read k ((x.bits.flatMap (fun b => [true, b])) ++ false :: rest) =
      if x.size ≤ k then some x else none := by
  simpa only [payload, Nat.size_eq_bits_len, fold_bits] using read_payload k x.bits rest

theorem readAtMost_encoded (cap x : ℕ) (rest : List Bool) :
    readAtMost cap ((x.bits.flatMap (fun b => [true, b])) ++ false :: rest) =
      if x ≤ cap then some x else none := by
  rw [readAtMost, read_encoded]
  by_cases hx : x ≤ cap
  · simp [hx, Nat.size_le_size hx]
  · by_cases hs : x.size ≤ cap.size <;> simp [hs, hx]

end BoundedBinaryInput

end BoundedBinaryInput

section LogCostRAMBinaryRead

namespace TargetedSamplers.Structured.BinaryRead

/-- Registers in order: input cursor, accumulator, binary place value, continuation
marker, digit, zero and one. The input and following fields may be arbitrarily long. -/
structure Reading (r : Fin 7 ↪ ℕ) (s : Store) (p a w m : ℕ) : Prop where
  pos : s.mem (r 0) = p
  acc : s.mem (r 1) = a
  place : s.mem (r 2) = w
  mark : s.mem (r 3) = m
  zero : s.mem (r 5) = 0
  one : s.mem (r 6) = 1

private theorem bit_width (v : Option Bool) : (bitVal v).size ≤ 2 := by
  cases v with
  | none => decide
  | some x => cases x <;> decide

set_option maxHeartbeats 700000 in
/-- One continuation marker causes a digit read, one accumulation at its place value, and
a lookahead to the following marker. No length instruction is used. -/
theorem oneDigit_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} {s : Store} {p a w : ℕ} (x : Bool)
    (h : Reading r s p a w 1) (input : τ.input[p+1]? = some x) (fit : s.Fits b) (hb : 2 ≤ b)
    (hp : (p+2).size ≤ b) (ha : (a+w).size ≤ b) (hw : (w+w).size ≤ b) :
    let u := ((oneDigit r).run τ s).last
    ∃ j ≤ 8, Exec τ (fun st => st.Fits b) (oneDigit r).cmd s u j ∧
      Reading r u (p+2) (if x then a+w else a) (w+w) (bitVal τ.input[p+2]?) ∧
      u.out = s.out ∧ ∀ addr, (∀ i, addr ≠ r i) → u.mem addr = s.mem addr := by
  let u := ((oneDigit r).run τ s).last
  have heq (i j : Fin 7) : r i = r j ↔ i = j := r.injective.eq_iff
  have hp' := (Nat.size_le_size (by omega : p+1 ≤ p+2)).trans hp
  have hm := (bit_width τ.input[p+2]?).trans hb
  have val (y : Bool) : bitVal (some y) = y.toNat := rfl
  have two : p+1+1 = p+2 := rfl
  have width : ((oneDigit r).run τ s).writeWidth ≤ b := by
    cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,h.acc,h.place,input,val,two,hp,hp',ha,hw,hm] <;> omega
  have ex := (oneDigit r).exec τ s b fit width
  refine ⟨_,?_,ex,?_,?_,?_⟩
  · cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,input,val]
  · cases x <;> constructor <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,h.acc,h.place,input,val,two]
  · cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,input,val]
  · intro addr hfree
    cases x <;> simp [oneDigit,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,heq,h.pos,h.zero,h.one,h.acc,h.place,input,val,hfree]

def pairs (xs : List Bool) := xs.flatMap fun x => [true,x]

theorem bitVal_marker (xs rest : List Bool) : bitVal (pairs xs ++ false::rest)[0]? = marker xs := by
  cases xs <;> rfl

/-- A field's payload followed by its terminator is scanned in at most ten steps per
digit and one final guard. The proof frames the next field on the input tape. -/
theorem scan_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} (xs rest : List Bool) (p a w : ℕ) (s : Store)
    (h : Reading r s p a w (marker xs)) (fit : s.Fits b) (hb : 2 ≤ b)
    (input : τ.input.drop p = pairs xs ++ false::rest) (hp : (p+2*xs.length).size ≤ b)
    (hplace : (w*2^xs.length).size ≤ b) (hdata : (a+w*(2^xs.length-1)).size ≤ b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (scan r) s t j ∧ j ≤ 10*xs.length+1 ∧
      Reading r t (p+2*xs.length) (a+w*xs.foldr Nat.bit 0) (w*2^xs.length) 0 ∧
      t.out = s.out ∧ ∀ addr, (∀ i, addr ≠ r i) → t.mem addr = s.mem addr := by
  induction xs generalizing p a w s with
  | nil =>
    refine ⟨s,1,.done (by rw [h.mark,h.zero]; decide),by simp,?_,rfl,fun _ _ => rfl⟩
    simpa [marker] using h
  | cons x xs ih =>
    have hi : τ.input[p+1]? = some x := by rw [← List.getElem?_drop,input]; rfl
    have remaining : τ.input.drop (p+2) = pairs xs ++ false::rest := by rw [← List.drop_drop,input]; rfl
    have mark : bitVal τ.input[p+2]? = marker xs := by
      have eq : τ.input[p+2]? = (τ.input.drop (p+2))[0]? := by simp
      rw [eq,remaining,bitVal_marker]
    have sp : p+2+2*xs.length = p+2*(x::xs).length := by simp; omega
    have hx : 1 ≤ 2^xs.length := Nat.one_le_two_pow
    have hplaces : (w+w)*2^xs.length = w*2^(x::xs).length := by simp [pow_succ]; ring
    have rem : 2^(x::xs).length-1 = 1+2*(2^xs.length-1) := by simp only [List.length_cons,pow_succ]; omega
    have ha : (a+w).size ≤ b := (Nat.size_le_size (by
      rw [rem]; simp only [Nat.mul_add,Nat.mul_one]; omega)).trans hdata
    have hw : (w+w).size ≤ b := (Nat.size_le_size (by
      rw [← hplaces]; simpa using Nat.mul_le_mul_left (w+w) hx)).trans hplace
    have hp' := (Nat.size_le_size (show p+2 ≤ p+2*(x::xs).length by simp)).trans hp
    obtain ⟨l,hl,ex,hr,log,frame⟩ := oneDigit_exec r x h hi fit hb hp' ha hw
    rw [mark] at hr
    let next := if x then a+w else a
    have hd : (next+(w+w)*(2^xs.length-1)).size ≤ b := by
      apply (Nat.size_le_size ?_).trans hdata
      rw [rem]
      cases x <;> dsimp [next] <;> nlinarith only [Nat.zero_le w]
    obtain ⟨t,j,loop,hj,out,hlog,save⟩ := ih (p+2) next (w+w) _ hr (ex.post fit) remaining
      (by rwa [sp]) (by rwa [hplaces]) hd
    refine ⟨t,_,.again (by rw [h.mark,h.zero]; change ¬(1:ℕ) ≤ 0; decide) ex loop,by simp; omega,?_,hlog.trans log,
      fun addr ha => (save addr ha).trans (frame addr ha)⟩
    have value : next+(w+w)*xs.foldr Nat.bit 0 = a+w*(x::xs).foldr Nat.bit 0 := by
      cases x <;> simp [next,Nat.bit] <;> ring
    simpa only [sp,value,hplaces] using out

theorem begin_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} {s : Store} {p : ℕ}
    (ptr : s.mem (r 0) = p) (xs rest : List Bool) (bits : τ.input.drop p = pairs xs ++ false::rest)
    (fit : s.Fits b) (hb : 2 ≤ b) :
    let t := ((beginField r).run τ s).last
    Exec τ (fun st => st.Fits b) (beginField r).cmd s t 5 ∧ Reading r t p 0 1 (marker xs) ∧
      t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have ne (i j : Fin 7) : r i = r j ↔ i = j := r.injective.eq_iff
  have hm : bitVal τ.input[p]? = marker xs := by
    have eq : (τ.input.drop p)[0]? = τ.input[p]? := by simp
    rw [← eq,bits,bitVal_marker]
  have width : ((beginField r).run τ s).writeWidth ≤ b := by
    have hv := (bit_width τ.input[p]?).trans hb
    simp [beginField,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,ne,ptr,hv] <;> omega
  refine ⟨(beginField r).exec τ s b fit width,?_,rfl,?_⟩
  · constructor <;> simp [beginField,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,ne,ptr,hm]
  · intro a ha
    simp [beginField,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,ha]

/-- Decode a canonical little-endian field, advancing to its successor. The contents and
length of the suffix never enter the instruction, time or word-width bound. -/
theorem readField_exec (r : Fin 7 ↪ ℕ) {τ : Tapes} {b : ℕ} (p x : ℕ) (rest : List Bool) (s : Store)
    (ptr : s.mem (r 0) = p) (input : τ.input.drop p = pairs x.bits ++ false::rest) (fit : s.Fits b)
    (hb : 2 ≤ b) (hp : (p+2*x.size+1).size ≤ b) (hw : x.size+1 ≤ b) :
    ∃ t j, Exec τ (fun st => st.Fits b) (readField r) s t j ∧ j ≤ 10*x.size+7 ∧
      t.mem (r 0) = p+2*x.size+1 ∧ t.mem (r 1) = x ∧ t.mem (r 5) = 0 ∧ t.mem (r 6) = 1 ∧ t.out = s.out ∧
      ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  obtain ⟨init,hr,oi,fi⟩ := begin_exec (τ := τ) r ptr x.bits rest input fit hb
  have place : ((1:ℕ)*2^x.bits.length).size ≤ b := by simpa [Nat.size_eq_bits_len,Nat.size_pow] using hw
  have data : (0+1*(2^x.bits.length-1)).size ≤ b := by
    simp only [Nat.zero_add,Nat.one_mul] at place ⊢
    exact (Nat.size_le_size (Nat.sub_le ..)).trans place
  have range : (p+2*x.bits.length).size ≤ b := by
    rw [Nat.size_eq_bits_len]; exact (Nat.size_le_size (by omega)).trans hp
  obtain ⟨u,l,loop,hl,post,ou,fu⟩ := scan_exec (τ := τ) r x.bits rest p 0 1 _ hr (init.post fit) hb input range place data
  let t := u.write (r 0) (p+2*x.size+1)
  have eq : (Op.add (r 0) (r 0) (r 6)).eval τ u = t := by
    simp [Op.eval,t,post.pos,post.one,Nat.size_eq_bits_len]
  have last : Exec τ (fun v => v.Fits b) (.op (.add (r 0) (r 0) (r 6))) u t 1 := by
    simpa only [eq] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) u (.add (r 0) (r 0) (r 6))
      (by rw [eq]; exact Store.write_fits (loop.post (init.post fit)) _ hp))
  rw [Nat.size_eq_bits_len] at hl
  refine ⟨t,_,init.seq (loop.seq last),by omega,by simp [t,Store.write],?_,?_,?_,ou.trans oi,?_⟩
  · simpa [t,Store.write,r.injective.ne (by decide : (1:Fin 7) ≠ 0),BoundedBinaryInput.fold_bits] using post.acc
  · simpa [t,Store.write,r.injective.ne (by decide : (5:Fin 7) ≠ 0)] using post.zero
  · simpa [t,Store.write,r.injective.ne (by decide : (6:Fin 7) ≠ 0)] using post.one
  · intro a ha
    simpa [t,Store.write,ha] using (fu a ha).trans (fi a ha)

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMBinaryRead

section LogCostRAMFieldArray

namespace TargetedSamplers.Structured.BinaryRead

def field (x : ℕ) := pairs x.bits ++ [false]

def fields (xs : List ℕ) := xs.flatMap field

theorem field_length (x : ℕ) : (field x).length = 2*x.size+1 := by
  have h (bs : List Bool) : (pairs bs).length = 2*bs.length := by
    induction bs with
    | nil => rfl
    | cons y ys ih =>
      change (pairs ys).length+1+1 = 2*(ys.length+1)
      rw [ih]; omega
  simp [field,h,Nat.size_eq_bits_len]

def fieldWork (xs : List ℕ) := (xs.map (fun x => 10*x.size+12)).sum

/-- Decode a stream of self-delimiting natural numbers directly into consecutive memory
words. The following input suffix is never read, even to find its length. -/
theorem readFields_exec (r : Fin 7 ↪ ℕ) (count dest : ℕ) (cd : count ≠ dest)
    (cr : ∀ i, count ≠ r i) (dr : ∀ i, dest ≠ r i) {τ : Tapes} {width : ℕ}
    (xs : List ℕ) (rest : List Bool) (p dst : ℕ) (s : Store)
    (ptr : s.mem (r 0) = p) (hc : s.mem count = xs.length) (hd : s.mem dest = dst)
    (hz : s.mem (r 5) = 0) (fit : s.Fits width) (hb : 2 ≤ width)
    (data : ∀ x ∈ xs, x.size+1 ≤ width) (hw : (p+(fields xs).length).size ≤ width)
    (dw : (dst+xs.length).size ≤ width) (low : count < dst ∧ dest < dst ∧ ∀ i, r i < dst)
    (input : τ.input.drop p = fields xs ++ rest) :
    ∃ t j, Exec τ (fun st => st.Fits width) (readFields r count dest) s t j ∧ j ≤ fieldWork xs+1 ∧
      t.mem (r 0) = p+(fields xs).length ∧ t.mem count = 0 ∧ t.mem dest = dst+xs.length ∧
      (∀ i (hi : i < xs.length), t.mem (dst+i) = xs[i]) ∧ t.out = s.out ∧
      ∀ a, a ≠ count → a ≠ dest → (∀ i, a ≠ r i) → (a < dst ∨ dst+xs.length ≤ a) → t.mem a = s.mem a := by
  induction xs generalizing s p dst with
  | nil =>
    exact ⟨s,1,.done (by rw [hc,hz]; rfl),by simp [fieldWork],by simpa [fields] using ptr,hc,
      by simpa using hd,by simp,rfl,fun _ _ _ _ _ => rfl⟩
  | cons x xs ih =>
    let next := p+(field x).length
    have parts : fields (x::xs) = field x ++ fields xs := rfl
    have sum : p+(fields (x::xs)).length = next+(fields xs).length := by simp [parts,next,Nat.add_assoc]
    have hinput : τ.input.drop p = pairs x.bits ++ false :: (fields xs++rest) := by
      simpa [parts,field,List.append_assoc] using input
    have midSize : (p+2*x.size+1).size ≤ width := by
      apply (Nat.size_le_size ?_).trans hw
      simp [parts,field_length]; omega
    obtain ⟨u,k,read,hk,pu,au,zu,ou,outu,frame⟩ := readField_exec (τ := τ) r p x (fields xs++rest) s ptr
      hinput fit hb midSize (data x (by simp))
    have fu := read.post fit
    have uc := (frame count cr).trans hc
    have ud := (frame dest dr).trans hd
    let u₁ := u.write dst x
    let u₂ := u₁.write dest (dst+1)
    let v := u₂.write count xs.length
    have ed : (Op.store dest (r 1)).eval τ u = u₁ := by simp [Op.eval,u₁,au,ud]
    have f₁ : u₁.Fits width := Store.write_fits fu dst (au ▸ fu (r 1))
    have st : Exec τ (fun z => z.Fits width) (.op (.store dest (r 1))) u u₁ 1 := by
      simpa only [ed] using (Exec.op (τ := τ) (inv := fun z => z.Fits width) u (.store dest (r 1)) (by rwa [ed]))
    have saved (a : ℕ) (ha : a < dst) : u₁.mem a = u.mem a := by simp [u₁,Store.write,ha.ne]
    have einc : (Op.add dest dest (r 6)).eval τ u₁ = u₂ := by
      simp [Op.eval,u₂,saved dest low.2.1,saved (r 6) (low.2.2 6),ud,ou]
    have f₂ : u₂.Fits width := Store.write_fits f₁ _ ((Nat.size_le_size (by simp : dst+1 ≤ dst+(x::xs).length)).trans dw)
    have inc : Exec τ (fun z => z.Fits width) (.op (.add dest dest (r 6))) u₁ u₂ 1 := by
      simpa only [einc] using (Exec.op (τ := τ) (inv := fun z => z.Fits width) u₁ (.add dest dest (r 6)) (by rwa [einc]))
    have saved' (a : ℕ) (ha : a < dst) (hne : a ≠ dest) : u₂.mem a = u.mem a := by
      simpa [u₂,Store.write,hne] using saved a ha
    have edec : (Op.sub count count (r 6)).eval τ u₂ = v := by
      simp [Op.eval,v,saved' count low.1 cd,saved' (r 6) (low.2.2 6) (dr 6).symm,uc,ou]
    have cw : xs.length.size ≤ width :=
      (Nat.size_le_size (show xs.length ≤ (x::xs).length by simp)).trans (uc ▸ fu count)
    have fv : v.Fits width := Store.write_fits f₂ count cw
    have dec : Exec τ (fun z => z.Fits width) (.op (.sub count count (r 6))) u₂ v 1 := by
      simpa only [edec] using (Exec.op (τ := τ) (inv := fun z => z.Fits width) u₂ (.sub count count (r 6)) (by rwa [edec]))
    have reg (i : Fin 7) : v.mem (r i) = u.mem (r i) := by
      simpa [v,Store.write,(cr i).symm] using saved' (r i) (low.2.2 i) (dr i).symm
    have unaffected (a : ℕ) (hc' : a ≠ count) (hd' : a ≠ dest) (ha : ∀ i, a ≠ r i) (n : a ≠ dst) :
        v.mem a = s.mem a := by simpa [v,u₂,u₁,Store.write,hc',hd',n] using frame a ha
    have pnext : v.mem (r 0) = next := by simpa [next,field_length,Nat.add_assoc] using (reg 0).trans pu
    have nextInput : τ.input.drop next = fields xs++rest := by
      rw [show next = p+(field x).length from rfl, ← List.drop_drop,input,parts,List.append_assoc,List.drop_left]
    obtain ⟨t,j,loop,hj,pt,ct,dt,words,ot,fr⟩ := ih next (dst+1) v pnext (by simp [v,Store.write])
      (by simp [v,u₂,Store.write,cd.symm]) ((reg 5).trans zu) fv (fun y hy => data y (by simp [hy]))
      (sum ▸ hw) (by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using dw)
      ⟨by have := low.1; omega,by have := low.2.1; omega,fun i => by have := low.2.2 i; omega⟩ nextInput
    have body := read.seq (st.seq (inc.seq dec))
    have go : ¬s.mem count ≤ s.mem (r 5) := by simp [hc,hz]
    refine ⟨t,_,.again go body loop,?_,sum ▸ pt,ct,?_,?_,ot.trans outu,?_⟩
    · simp only [fieldWork,List.map_cons,List.sum_cons] at hj ⊢
      omega
    · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using dt
    · intro i hi
      cases i with
      | zero =>
        have old := fr dst low.1.ne.symm low.2.1.ne.symm (fun i => (low.2.2 i).ne.symm) (.inl (by omega))
        simpa [v,u₂,u₁,Store.write,low.1.ne.symm,low.2.1.ne.symm] using old
      | succ i => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using words i (by simpa using hi)
    · intro a nc nd nr out
      have sh : a < dst+1 ∨ dst+1+xs.length ≤ a := by simp only [List.length_cons] at out; omega
      exact (fr a nc nd nr sh).trans (unaffected a nc nd nr (by simp only [List.length_cons] at out; omega))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMFieldArray

section LogCostRAMGraphHeader

namespace TargetedSamplers.Structured.BinaryRead

private theorem reserved (r : Fin 11 ↪ ℕ) (a : Fin 11) (large : 7 ≤ a.val) (i : Fin 7) :
    r a ≠ digitRegs r i := by
  intro h
  have e := congrArg Fin.val (r.injective h)
  change a.val = i.val at e
  have := i.isLt
  omega

private theorem countEdges_exec {τ : Tapes} (r : Fin 11 ↪ ℕ) {s : Store} {w m : ℕ} (fit : s.Fits w)
    (val : s.mem (r 1) = m) (zero : s.mem (r 5) = 0) (one : s.mem (r 6) = 1) (width : (3*m+2).size ≤ w) :
    let t := ((countEdges r).run τ s).last
    Exec τ (fun v => v.Fits w) (countEdges r).cmd s t 5 ∧ t.mem (r 8) = m ∧ t.mem (r 9) = 3*m+2 ∧
      t.out = s.out ∧ ∀ a, a ≠ r 8 → a ≠ r 9 → t.mem a = s.mem a := by
  have eq (i j : Fin 11) : r i = r j ↔ i = j := r.injective.eq_iff
  have a := (Nat.size_le_size (by omega : m ≤ 3*m+2)).trans width
  have b := (Nat.size_le_size (by omega : m+m ≤ 3*m+2)).trans width
  have c := (Nat.size_le_size (by omega : m+m+m ≤ 3*m+2)).trans width
  have d := (Nat.size_le_size (by omega : m+m+m+1 ≤ 3*m+2)).trans width
  have e : m+m+m+1+1 = 3*m+2 := by omega
  have hw : ((countEdges r).run τ s).writeWidth ≤ w := by
    simp [countEdges,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,val,zero,one,a,b,c,d,e,width]
  refine ⟨(countEdges r).exec τ s w fit hw,?_,?_,rfl,?_⟩
  · simp [countEdges,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      eq,val,zero]
  · simp [countEdges,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      eq,val,zero,one,e]
  · intro addr h₁ h₂
    simp [countEdges,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,h₁,h₂]

/-- Read both dimensions and exactly 3m+2 natural fields in one fixed RAM program.
The destination contains the original words in order and the input cursor stops at the
first bit of the suffix. It never reads the total input length. -/
theorem graphHeader_exec {τ : Tapes} (r : Fin 11 ↪ ℕ) {width : ℕ} (s : Store) (p dst n m : ℕ) (xs : List ℕ)
    (suffix : List Bool) (hxs : xs.length = 3*m+2) (input : τ.input.drop p =
      field n ++ (field m ++ (fields xs ++ suffix))) (ptr : s.mem (r 0) = p) (dest : s.mem (r 10) = dst)
    (sep : ∀ i, r i < dst) (fit : s.Fits width) (hb : 2 ≤ width)
    (hnw : n.size+1 ≤ width) (hmw : m.size+1 ≤ width) (hcount : (3*m+2).size ≤ width)
    (hdw : (dst+xs.length).size ≤ width) (each : ∀ x ∈ xs, x.size+1 ≤ width)
    (hpw : (p+(field n).length+(field m).length+(fields xs).length).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (graphHeader r) s t j ∧
      j ≤ 10*n.size+10*m.size+fieldWork xs+21 ∧ t.mem (r 7) = n ∧ t.mem (r 8) = m ∧
      t.mem (r 0) = p+(field n).length+(field m).length+(fields xs).length ∧
      t.mem (r 10) = dst+xs.length ∧ (∀ i (hi : i < xs.length), t.mem (dst+i) = xs[i]) ∧ t.out = s.out ∧
      ∀ a, (∀ i, a ≠ r i) → (a < dst ∨ dst+xs.length ≤ a) → t.mem a = s.mem a := by
  let rr := digitRegs r
  have res (a : Fin 11) (h : 7 ≤ a.val) : ∀ i, r a ≠ rr i := reserved r a h
  have eq {i j : Fin 11} (d : i ≠ j) := r.injective.ne d
  let p₁ := p+(field n).length
  let p₂ := p₁+(field m).length
  have hwn : (p+2*n.size+1).size ≤ width := by
    apply (Nat.size_le_size ?_).trans hpw; rw [field_length n]; omega
  have hwm : (p₁+2*m.size+1).size ≤ width := by
    apply (Nat.size_le_size ?_).trans hpw; dsimp [p₁]; rw [field_length m]; omega
  have inN : τ.input.drop p = pairs n.bits ++ false::(field m ++ (fields xs ++ suffix)) := by
    simpa only [field,List.append_assoc,List.singleton_append] using input
  obtain ⟨u₀,j₀,readN,bn,posN,valueN,zeroN,_,outN,frN⟩ :=
    readField_exec (τ := τ) rr p n _ s ptr inN fit hb hwn hnw
  let u := u₀.write (r 7) n
  have vn : u₀.mem (r 1) = n := valueN
  have zn : u₀.mem (r 5) = 0 := zeroN
  have en : (Op.add (r 7) (r 1) (r 5)).eval τ u₀ = u := by simp [Op.eval,u,vn,zn]
  have fu : u.Fits width := Store.write_fits (readN.post fit) _ (by omega)
  have saveN : Exec τ (fun st => st.Fits width) (.op (.add (r 7) (r 1) (r 5))) u₀ u 1 := by
    simpa only [en] using (Exec.op (τ := τ) (inv := fun st => st.Fits width) u₀ (.add (r 7) (r 1) (r 5)) (by rwa [en]))
  have pu : u.mem (rr 0) = p₁ := by
    simpa [u,Store.write,(res 7 (by decide) 0).symm,p₁,field_length,Nat.add_assoc] using posN
  have inM₀ : τ.input.drop p₁ = field m ++ (fields xs ++ suffix) := by
    rw [show p₁ = p+(field n).length from rfl, ← List.drop_drop,input,List.drop_left]
  have inM : τ.input.drop p₁ = pairs m.bits ++ false::(fields xs ++ suffix) := by
    simpa only [field,List.append_assoc,List.singleton_append] using inM₀
  obtain ⟨v,j₁,readM,bm,posM,valueM,zeroM,oneM,outM,frM⟩ :=
    readField_exec (τ := τ) rr p₁ m _ u pu inM fu hb hwm hmw
  obtain ⟨counter,vm,vc,oc,fc⟩ := countEdges_exec (τ := τ) r (readM.post fu) valueM zeroM oneM hcount
  let v' := ((countEdges r).run τ v).last
  have vp : v'.mem (rr 0) = p₂ := by
    simpa [p₂,field_length,Nat.add_assoc] using
      (fc _ (res 8 (by decide) 0).symm (res 9 (by decide) 0).symm).trans posM
  have vz : v'.mem (rr 5) = 0 := (fc _ (res 8 (by decide) 5).symm (res 9 (by decide) 5).symm).trans zeroM
  have unchanged (a : ℕ) (out : ∀ i, a ≠ rr i) (n7 : a ≠ r 7) (n8 : a ≠ r 8) (n9 : a ≠ r 9) :
      v'.mem a = s.mem a := by
    rw [show v'.mem a = v.mem a from fc _ n8 n9,frM _ out]
    simpa [u,Store.write,n7] using frN a out
  have vd := (unchanged (r 10) (res 10 (by decide)) (eq (by decide)) (eq (by decide)) (eq (by decide))).trans dest
  have inWords : τ.input.drop p₂ = fields xs ++ suffix := by
    rw [show p₂ = p₁+(field m).length from rfl,← List.drop_drop,inM₀,List.drop_left]
  obtain ⟨t,j,loop,bound,last,_,td,words,ot,ft⟩ :=
    readFields_exec (τ := τ) rr (r 9) (r 10) (eq (by decide)) (res 9 (by decide)) (res 10 (by decide)) xs
      suffix p₂ dst v' vp (vc.trans hxs.symm) vd vz (counter.post (readM.post fu)) hb each hpw hdw
      ⟨sep 9,sep 10,fun i => sep ⟨i.val,by have := i.isLt; omega⟩⟩ inWords
  have nval : v'.mem (r 7) = n := by
    rw [show v'.mem (r 7) = v.mem (r 7) from fc _ (eq (by decide)) (eq (by decide)),frM _ (res 7 (by decide))]
    simp [u,Store.write]
  refine ⟨t,_,readN.seq (saveN.seq (readM.seq (counter.seq loop))),by omega,
    (ft _ (eq (by decide)) (eq (by decide)) (res 7 (by decide)) (.inl (sep 7))).trans nval,
    (ft _ (eq (by decide)) (eq (by decide)) (res 8 (by decide)) (.inl (sep 8))).trans vm,
    last,td,words,ot.trans (oc.trans (outM.trans outN)),?_⟩
  intro a free after
  have small (i : Fin 7) : a ≠ rr i := free ⟨i.val,by have := i.isLt; omega⟩
  exact (ft a (free 9) (free 10) small after).trans (unchanged a small (free 7) (free 8) (free 9))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMGraphHeader

section LogCostRAMCappedRead

namespace TargetedSamplers.Structured.BinaryRead

/-- Read exactly the low prefix while its places fit. The continuation starts at the
following marker. It can terminate or reject without inspecting the remaining payload. -/
theorem prefix_exec (r : Fin 7 ↪ ℕ) (limit fail : ℕ) (separate : ∀ i, limit ≠ r i)
    {τ : Tapes} {width : ℕ} (pre tail rest : List Bool) (p a start cap : ℕ) (s : Store)
    (h : Reading r s p a (2^start) (marker (pre++tail))) (fit : s.Fits width)
    (lim : s.mem limit = cap) (ha : a < 2^start) (hcap : start+pre.length ≤ cap.size)
    (hb : 2 ≤ width) (bw : cap.size+1 ≤ width) (pw : (p+2*pre.length).size ≤ width)
    (input : τ.input.drop p = pairs (pre++tail) ++ false::rest) :
    ∃ u j, j ≤ 11*pre.length ∧
      Reading r u (p+2*pre.length) (a+2^start*pre.foldr Nat.bit 0) (2^(start+pre.length)) (marker tail) ∧
      u.Fits width ∧ u.out = s.out ∧ (∀ addr, (∀ i, addr ≠ r i) → u.mem addr = s.mem addr) ∧
      ∀ t k, Exec τ (fun st => st.Fits width) (cappedScan r limit fail) u t k →
        Exec τ (fun st => st.Fits width) (cappedScan r limit fail) s t (j+k) := by
  induction pre generalizing p a start s with
  | nil => exact ⟨s,0,by simp,by simpa using h,fit,rfl,fun _ _ => rfl,fun t k ex => by simpa using ex⟩
  | cons x pre ih =>
    have hi : τ.input[p+1]? = some x := by rw [← List.getElem?_drop,input]; rfl
    have remaining : τ.input.drop (p+2) = pairs (pre++tail) ++ false::rest := by rw [← List.drop_drop,input]; rfl
    have mark : bitVal τ.input[p+2]? = marker (pre++tail) := by
      have eq : τ.input[p+2]? = (τ.input.drop (p+2))[0]? := by simp
      rw [eq,remaining,bitVal_marker]
    have jcap : start < cap.size := by simp only [List.length_cons] at hcap; omega
    have pow : 2^start + 2^start = 2^(start+1) := by rw [pow_succ]; omega
    have hw : (2^start+2^start).size ≤ width := by rw [pow,Nat.size_pow]; omega
    have addWidth := (Nat.size_le_size (show a+2^start ≤ 2^start+2^start by omega)).trans hw
    have sp : p+2+2*pre.length = p+2*(x::pre).length := by simp; omega
    have hp := (Nat.size_le_size (show p+2 ≤ p+2*(x::pre).length by simp)).trans pw
    obtain ⟨l,hl,ex,hr,log,frame⟩ := oneDigit_exec r x h hi fit hb hp addWidth hw
    rw [mark,pow] at hr
    let next := if x then a+2^start else a
    have lt : next < 2^(start+1) := by rw [← pow]; cases x <;> dsimp [next] <;> omega
    obtain ⟨u,j,hj,rep,fu,ou,fr,cont⟩ := ih (p+2) next (start+1) _ hr (ex.post fit)
      ((frame limit separate).trans lim) lt (by simp only [List.length_cons] at hcap; omega) (by rwa [sp]) remaining
    have value : next+2^(start+1)*pre.foldr Nat.bit 0 = a+2^start*(x::pre).foldr Nat.bit 0 := by
      cases x <;> simp [next,Nat.bit,pow_succ] <;> ring
    have power : start+1+pre.length = start+(x::pre).length := by simp; omega
    refine ⟨u,l+3+j,by simp; omega,by simpa only [sp,value,power] using rep,fu,ou.trans log,
      fun addr ha => (fr addr ha).trans (frame addr ha),?_⟩
    intro t k ev
    have guard : ¬s.mem (r 3) ≤ s.mem (r 5) := by rw [h.mark,h.zero]; change ¬(1:ℕ) ≤ 0; decide
    have accept : s.mem (r 2) ≤ s.mem limit := by rw [h.place,lim]; exact Nat.lt_size.mp jcap
    have body := Exec.yes (n := Cmd.seq (.op (.const (r 3) 0)) (.op (.const fail 1))) accept ex
    rw [show l+3+j+k = 1+(1+l)+1+(j+k) by omega]
    exact Exec.again guard body (cont t k ev)

private theorem finish_scan (r : Fin 7 ↪ ℕ) (limit fail : ℕ) (fl : fail ≠ limit)
    (hl : ∀ i, limit ≠ r i) (hf : ∀ i, fail ≠ r i) {τ : Tapes} {width : ℕ} (s : Store) (p a w cap : ℕ)
    (tail : List Bool) (h : Reading r s p a w (marker tail)) (fit : s.Fits width) (hb : 2 ≤ width)
    (lim : s.mem limit = cap) (ok : s.mem fail = 0) (late : tail ≠ [] → cap < w) :
    ∃ t j, Exec τ (fun st => st.Fits width) (cappedScan r limit fail) s t j ∧ j ≤ 7 ∧
      t.mem fail = (if tail = [] then 0 else 1) ∧ t.mem (r 1) = a ∧ t.mem limit = cap ∧
      t.out = s.out ∧ ∀ z, z ≠ r 3 → z ≠ fail → t.mem z = s.mem z := by
  cases tail with
  | nil =>
    exact ⟨s,1,.done (by rw [h.mark,h.zero]; decide),by decide,by simpa using ok,h.acc,lim,rfl,fun _ _ _ => rfl⟩
  | cons x xs =>
    let u := s.write (r 3) 0
    let t := u.write fail 1
    have fu : u.Fits width := Store.write_fits fit _ (by simp)
    have ft : t.Fits width := Store.write_fits fu _ (by simp; omega)
    have zero : Exec τ (fun st => st.Fits width) (.op (.const (r 3) 0)) s u 1 := .op _ _ fu
    have bad : Exec τ (fun st => st.Fits width) (.op (.const fail 1)) u t 1 := .op _ _ ft
    have gt : ¬s.mem (r 2) ≤ s.mem limit := by rw [h.place,lim]; exact Nat.not_le_of_lt (late (by simp))
    have guard : ¬s.mem (r 3) ≤ s.mem (r 5) := by rw [h.mark,h.zero]; change ¬(1:ℕ) ≤ 0; decide
    have frame (z : ℕ) (h3 : z ≠ r 3) (hb' : z ≠ fail) : t.mem z = s.mem z := by simp [t,u,Store.write,h3,hb']
    have mark : t.mem (r 3) = 0 := by simp [t,u,Store.write,(hf 3).symm]
    have unit := (frame (r 5) (r.injective.ne (by decide : (5:Fin 7) ≠ 3)) (hf 5).symm).trans h.zero
    have done : Exec τ (fun st => st.Fits width) (cappedScan r limit fail) t t 1 := .done (by rw [mark,unit])
    refine ⟨t,_,.again guard (.no gt (zero.seq bad)) done,by decide,by simp [t,Store.write],
      (frame _ (r.injective.ne (by decide : (1:Fin 7) ≠ 3)) (hf 1).symm).trans h.acc,
      (frame _ (hl 3) fl.symm).trans lim,rfl,frame⟩

/-- Read a canonical natural and reject exactly the numbers above cap. The bounds depend
only on cap and the starting address, even when the encoded integer has arbitrarily many digits. -/
theorem readAtMost_exec (r : Fin 7 ↪ ℕ) (limit fail : ℕ) (fl : fail ≠ limit)
    (hl : ∀ i, limit ≠ r i) (hf : ∀ i, fail ≠ r i) {τ : Tapes} {width : ℕ} (s : Store)
    (p x cap : ℕ) (rest : List Bool) (lim : s.mem limit = cap) (ptr : s.mem (r 0) = p)
    (fit : s.Fits width) (hb : 2 ≤ width) (bw : cap.size+1 ≤ width) (pw : (p+2*cap.size).size ≤ width)
    (input : τ.input.drop p = pairs x.bits ++ false::rest) :
    ∃ t j, Exec τ (fun st => st.Fits width) (readAtMost r limit fail) s t j ∧ j ≤ 11*cap.size+16 ∧
      (t.mem fail = 0 ↔ x ≤ cap) ∧ (x ≤ cap → t.mem (r 1) = x) ∧ t.out = s.out ∧
      ∀ addr, addr ≠ fail → (∀ i, addr ≠ r i) → t.mem addr = s.mem addr := by
  let s₀ := s.write fail 0
  have f₀ : s₀.Fits width := Store.write_fits fit _ (by simp)
  have clean : Exec τ (fun st => st.Fits width) (.op (.const fail 0)) s s₀ 1 := .op _ _ f₀
  have keep₀ (a : ℕ) (ha : a ≠ fail) : s₀.mem a = s.mem a := by simp [s₀,Store.write,ha]
  let pre := x.bits.take cap.size
  let tail := x.bits.drop cap.size
  have split : pre++tail = x.bits := List.take_append_drop ..
  have plen : pre.length ≤ cap.size := by simp [pre]
  have pw' : (p+2*pre.length).size ≤ width := (Nat.size_le_size (by omega)).trans pw
  obtain ⟨init,hr,oi,fi⟩ := begin_exec (τ := τ) r ((keep₀ _ (hf 0).symm).trans ptr) x.bits rest input f₀ hb
  let s₁ := ((beginField r).run τ s₀).last
  have stable (a : ℕ) (ha : ∀ i, a ≠ r i) : s₁.mem a = s₀.mem a := fi a ha
  have limits := (stable limit hl).trans ((keep₀ limit fl.symm).trans lim)
  have start : Reading r s₁ p 0 (2^0) (marker (pre++tail)) := by simpa only [split,pow_zero] using hr
  obtain ⟨u,k,hk,rep,fu,ou,fr,cont⟩ := prefix_exec r limit fail hl (τ := τ) pre tail rest p 0 0 cap s₁ start
    (init.post f₀) limits (by decide) (by simpa using plen) hb bw pw' (by rwa [split])
  have reg : Reading r u (p+2*pre.length) (pre.foldr Nat.bit 0) (2^pre.length) (marker tail) := by simpa using rep
  have uh : u.mem fail = 0 := by rw [fr fail hf,stable fail hf]; simp [s₀,Store.write]
  have late (hn : tail ≠ []) : cap < 2^pre.length := by
    have hlong : cap.size < x.bits.length := by
      by_contra! h
      exact hn (List.drop_eq_nil_of_le h)
    simpa [pre,List.length_take,Nat.min_eq_left hlong.le] using Nat.lt_size_self cap
  obtain ⟨v,l,term,hl',failVal,acc,limitVal,out,frame⟩ := finish_scan r limit fail fl hl hf (τ := τ) u _ _ _ cap tail
    reg fu hb ((fr limit hl).trans limits) uh late
  have ev := cont v l term
  have short (hx : x ≤ cap) : pre = x.bits ∧ tail = [] := by
    have n : x.bits.length ≤ cap.size := by simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hx
    exact ⟨List.take_of_length_le n,List.drop_eq_nil_of_le n⟩
  have val (ht : tail = []) : v.mem (r 1) = x := by
    have all : pre = x.bits := by simpa [ht] using split
    simpa only [all,BoundedBinaryInput.fold_bits] using acc
  have main := clean.seq (init.seq ev)
  have ext (a : ℕ) (ha : a ≠ fail) (hs : ∀ i, a ≠ r i) : v.mem a = s.mem a :=
    (frame a (hs 3) ha).trans ((fr a hs).trans ((stable a hs).trans (keep₀ a ha)))
  have output : v.out = s.out := out.trans (ou.trans oi)
  by_cases test : v.mem (r 1) ≤ v.mem limit
  · have check : Exec τ (fun st => st.Fits width) (.branch (r 1) limit .skip (.op (.const fail 1))) v v 1 :=
      .yes test (.skip v)
    refine ⟨v,_,clean.seq (init.seq (ev.seq check)),by omega,?_,fun hx => val (short hx).2,output,ext⟩
    rw [failVal]
    by_cases ht : tail = []
    · have le : x ≤ cap := by simpa [val ht,limitVal] using test
      simp [ht,le]
    · have gt : ¬x ≤ cap := fun h => ht (short h).2
      simp [ht,gt]
  · let t := v.write fail 1
    have ff := Store.write_fits (main.post fit) fail (show (1:ℕ).size ≤ width by simp; omega)
    have bad : Exec τ (fun st => st.Fits width) (.op (.const fail 1)) v t 1 := .op _ _ ff
    have check := Exec.no (y := Cmd.skip) test bad
    have gt : ¬x ≤ cap := by
      intro hx
      exact test (by rwa [val (short hx).2,limitVal])
    refine ⟨t,_,clean.seq (init.seq (ev.seq check)),by omega,by simp [t,Store.write,gt],
      fun hx => (gt hx).elim,output,?_⟩
    intro a ha hs; simpa [t,Store.write,ha] using ext a ha hs

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMCappedRead

section LogCostRAMSignedRead

namespace TargetedSamplers.Structured.BinaryRead

theorem readSigned_exec (r : Fin 7 ↪ ℕ) (limit fail : ℕ) (fl : fail ≠ limit)
    (hl : ∀ i, limit ≠ r i) (hf : ∀ i, fail ≠ r i) {τ : Tapes} {width : ℕ} (s : Store)
    (p x cap : ℕ) (sign : Bool) (rest : List Bool) (lim : s.mem limit = cap) (ptr : s.mem (r 0) = p)
    (fit : s.Fits width) (hb : 2 ≤ width) (bw : cap.size+1 ≤ width) (pw : (p+1+2*cap.size).size ≤ width)
    (input : τ.input.drop p = sign :: (pairs x.bits ++ false::rest)) :
    ∃ t j, Exec τ (fun st => st.Fits width) (readSigned r limit fail) s t j ∧ j ≤ 11*cap.size+21 ∧
      (t.mem fail = 0 ↔ sign = false ∧ x ≤ cap) ∧ (sign = false → x ≤ cap → t.mem (r 1) = x) ∧
      t.out = s.out ∧ ∀ addr, addr ≠ fail → (∀ i, addr ≠ r i) → t.mem addr = s.mem addr := by
  have ne {i j : Fin 7} (d : i ≠ j) := r.injective.ne d
  let zero := s.write (r 5) 0
  let u := zero.write (r 3) sign.toNat
  have m : τ.input[p]? = some sign := by
    have e : (τ.input.drop p)[0]? = τ.input[p]? := by simp
    rw [← e,input]; rfl
  have f₀ : zero.Fits width := Store.write_fits fit _ (by simp)
  have f₁ : u.Fits width := Store.write_fits f₀ _ (by cases sign <;> simp <;> omega)
  have e₀ : Exec τ (fun st => st.Fits width) (.op (.const (r 5) 0)) s zero 1 := .op _ _ f₀
  have eval : (Op.input (r 3) (r 0)).eval τ zero = u := by
    have ep : zero.mem (r 0) = p := by simpa [zero,Store.write,ne (by decide : (0:Fin 7) ≠ 5)] using ptr
    simp [Op.eval,u,ep,m,bitVal]
  have e₁ : Exec τ (fun st => st.Fits width) (.op (.input (r 3) (r 0))) zero u 1 := by
    simpa only [eval] using (Exec.op (τ := τ) (inv := fun st => st.Fits width) zero (.input (r 3) (r 0)) (by rwa [eval]))
  have tmp : u.mem (r 3) = sign.toNat := by simp [u,Store.write]
  have z : u.mem (r 5) = 0 := by simp [u,zero,Store.write,ne (by decide : (5:Fin 7) ≠ 3)]
  have normal (a : ℕ) (d5 : a ≠ r 5) (d3 : a ≠ r 3) : u.mem a = s.mem a := by simp [u,zero,Store.write,d3,d5]
  cases sign with
  | true =>
    let t := u.write fail 1
    have reject : Exec τ (fun st => st.Fits width) (.op (.const fail 1)) u t 1 :=
      .op _ _ (Store.write_fits f₁ _ (by simp; omega))
    have guard : ¬u.mem (r 3) ≤ u.mem (r 5) := by rw [tmp,z]; decide
    refine ⟨t,_,e₀.seq (e₁.seq (.no guard reject)),by omega,by simp [t,Store.write],by simp,rfl,?_⟩
    intro addr nf fr
    simpa [t,Store.write,nf] using normal addr (fr 5) (fr 3)
  | false =>
    let v := u.write (r 6) 1
    let w := v.write (r 0) (p+1)
    have fv : v.Fits width := Store.write_fits f₁ _ (by simp; omega)
    have fw : w.Fits width := Store.write_fits fv _ ((Nat.size_le_size (by omega)).trans pw)
    have set1 : Exec τ (fun st => st.Fits width) (.op (.const (r 6) 1)) u v 1 := .op _ _ fv
    have pp : v.mem (r 0) = p := by
      simpa [v,Store.write,ne (by decide : (0:Fin 7) ≠ 6)] using
        (normal (r 0) (ne (by decide : (0:Fin 7) ≠ 5)) (ne (by decide : (0:Fin 7) ≠ 3))).trans ptr
    have nxt : (Op.add (r 0) (r 0) (r 6)).eval τ v = w := by
      simp only [Op.eval,w,pp,show v.mem (r 6) = 1 by simp [v,Store.write]]
    have adv : Exec τ (fun st => st.Fits width) (.op (.add (r 0) (r 0) (r 6))) v w 1 := by
      simpa only [nxt] using (Exec.op (τ := τ) (inv := fun st => st.Fits width) v (.add (r 0) (r 0) (r 6)) (by rwa [nxt]))
    have keep (a : ℕ) (outside : ∀ i, a ≠ r i) : w.mem a = s.mem a := by
      simpa [w,v,Store.write,outside] using normal a (outside 5) (outside 3)
    have tail : τ.input.drop (p+1) = pairs x.bits ++ false::rest := by rw [← List.drop_drop,input]; rfl
    obtain ⟨t,k,read,hk,valid,value,out,frame⟩ := readAtMost_exec (τ := τ) r limit fail fl hl hf w
      (p+1) x cap rest ((keep limit hl).trans lim) (by simp [w,Store.write]) fw hb bw pw tail
    have guard : u.mem (r 3) ≤ u.mem (r 5) := by rw [tmp,z]; decide
    refine ⟨t,_,e₀.seq (e₁.seq (.yes guard (set1.seq (adv.seq read)))),by omega,by simpa using valid,
      fun _ hx => value hx,out,fun a nf fr => (frame a nf fr).trans (keep a fr)⟩

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMSignedRead

section HamiltonianInputFields

namespace DirectedHamiltonicity.Main

open TargetedSamplers.Structured.BinaryRead

theorem encodeParity_fields {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n) (B : ℤ) :
    encodeParityInstance n m tail head weight s t B =
      field n ++ (field m ++ (fields (arcFields tail head weight s t) ++ encInt B)) := by
  simp [encodeParityInstance,arcFields,fields,field,pairs,encNat,List.flatMap_assoc,List.append_assoc]

theorem arcFields_length {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n) :
    (arcFields tail head weight s t).length = 3*m+2 := by
  have h (es : List (Fin m)) : (es.flatMap fun e => [(tail e).val,(head e).val,weight e]).length = 3*es.length := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]
      omega
  simp [arcFields,h]

theorem arcFields_weight {n m : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n) (e : Fin m) :
    (arcFields tail head weight s t)[3*e.val+2]? = some (weight e) := by
  let trip := fun f : Fin m => [(tail f).val,(head f).val,weight f]
  have row (es : List (Fin m)) (j : ℕ) (hj : j < es.length) :
      (es.flatMap trip ++ [s.val,t.val])[3*j+2]? = some (weight es[j]) := by
    induction es generalizing j with
    | nil => simp at hj
    | cons a es ih =>
      cases j with
      | zero => rfl
      | succ j =>
        rw [show 3*(j+1)+2 = (3*j+2)+1+1+1 by omega]
        exact ih j (by simpa using hj)
  simpa [arcFields,trip] using row (List.finRange m) e.val (by simpa using e.isLt)

theorem arcFields_bound {n m W : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n)
    (hw : ∀ e, weight e ≤ W) : ∀ x ∈ arcFields tail head weight s t, x ≤ max n W := by
  intro x hx
  simp only [arcFields,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_flatMap] at hx
  rcases hx with ⟨e,_,rfl|rfl|rfl⟩ | rfl | rfl
  · exact (tail e).isLt.le.trans (le_max_left ..)
  · exact (head e).isLt.le.trans (le_max_left ..)
  · exact (hw e).trans (le_max_right ..)
  · exact s.isLt.le.trans (le_max_left ..)
  · exact t.isLt.le.trans (le_max_left ..)

/-- A uniform bound on both the number of input positions and the number of primitive
steps to load the edge table, independent of the target field and the coin tape. -/
theorem fields_bounds (xs : List ℕ) (M : ℕ) (h : ∀ x ∈ xs, x ≤ M) :
    (fields xs).length ≤ xs.length*(2*M.size+1) ∧ fieldWork xs ≤ xs.length*(10*M.size+12) := by
  induction xs with
  | nil => simp [fields,fieldWork]
  | cons x xs ih =>
    have le := Nat.size_le_size (h x (by simp))
    obtain ⟨h₁,h₂⟩ := ih fun y hy => h y (by simp [hy])
    change (field x ++ fields xs).length ≤ _ ∧ 10*x.size+12+fieldWork xs ≤ _
    simp only [List.length_append,field_length,List.length_cons]
    rw [Nat.succ_mul xs.length (2*M.size+1),Nat.succ_mul xs.length (10*M.size+12)]
    omega

/-- The sign is read even for an arbitrarily long target. A valid result in register 1
equals the requested weight, and the failure flag is set precisely outside [0, cap]. -/
theorem read_target_ram (r : Fin 7 ↪ ℕ) (limit fail : ℕ) (fl : fail ≠ limit)
    (hl : ∀ i, limit ≠ r i) (hf : ∀ i, fail ≠ r i) {τ : TargetedSamplers.Tapes} {width : ℕ}
    (s : TargetedSamplers.Structured.Store) (p cap : ℕ) (B : ℤ) (suffix : List Bool)
    (lim : s.mem limit = cap) (ptr : s.mem (r 0) = p) (fit : s.Fits width) (hb : 2 ≤ width)
    (bw : cap.size+1 ≤ width) (pw : (p+1+2*cap.size).size ≤ width) (input : τ.input.drop p = encInt B ++ suffix) :
    ∃ t j, TargetedSamplers.Structured.Exec τ (fun st => st.Fits width) (readSigned r limit fail) s t j ∧
      j ≤ 11*cap.size+21 ∧ (t.mem fail = 0 ↔ 0 ≤ B ∧ B ≤ (cap:ℤ)) ∧
      (0 ≤ B → B ≤ (cap:ℤ) → t.mem (r 1) = B.toNat) ∧ t.out = s.out ∧
      ∀ addr, addr ≠ fail → (∀ i, addr ≠ r i) → t.mem addr = s.mem addr := by
  have tape : τ.input.drop p = decide (B < 0)::(pairs B.natAbs.bits ++ false::suffix) := by
    simpa [encInt,encNat,pairs,List.append_assoc] using input
  obtain ⟨t,j,ex,work,ok,val,out,frame⟩ :=
    readSigned_exec (τ := τ) r limit fail fl hl hf s p B.natAbs cap (decide (B < 0)) suffix lim ptr fit hb bw pw tape
  refine ⟨t,j,ex,work,?_,?_,out,frame⟩
  · rw [ok]; cases B <;> simp [Int.ofNat_eq_natCast]
  · intro nonneg fits
    cases B with
    | ofNat n => exact val (by simp [Int.ofNat_eq_natCast]) (by simpa using fits)
    | negSucc n => omega

/-- Load the graph portion of the *posted* multigraph encoding. The cursor is left at the
sign of B; neither B nor the overall input length occurs in any resource hypothesis. -/
theorem read_graph_ram {n m W : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n)
    (hw : ∀ e, weight e ≤ W) (B : ℤ) (r : Fin 11 ↪ ℕ) {τ : TargetedSamplers.Tapes} {b : ℕ}
    (st : TargetedSamplers.Structured.Store) (p dst : ℕ) (suffix : List Bool)
    (input : τ.input.drop p = encodeParityInstance n m tail head weight s t B ++ suffix)
    (ptr : st.mem (r 0) = p) (dest : st.mem (r 10) = dst) (sep : ∀ i, r i < dst)
    (fit : st.Fits b) (hb : 2 ≤ b) (hm : m.size+1 ≤ b) (hn : (max n W).size+1 ≤ b)
    (hcount : (3*m+2).size ≤ b) (hd : (dst+(3*m+2)).size ≤ b)
    (hp : (p+(2*n.size+1)+(2*m.size+1)+(3*m+2)*(2*(max n W).size+1)).size ≤ b) :
    let xs := arcFields tail head weight s t
    ∃ u j, TargetedSamplers.Structured.Exec τ (fun v => v.Fits b) (graphHeader r) st u j ∧
      j ≤ 10*n.size+10*m.size+(3*m+2)*(10*(max n W).size+12)+21 ∧
      u.mem (r 7) = n ∧ u.mem (r 8) = m ∧
      u.mem (r 0) = p+(field n).length+(field m).length+(fields xs).length ∧
      τ.input.drop (u.mem (r 0)) = encInt B ++ suffix ∧
      u.mem (r 10) = dst+xs.length ∧ (∀ i (hi : i < xs.length),u.mem (dst+i) = xs[i]) ∧
      u.out = st.out ∧ ∀ a, (∀ i, a ≠ r i) → (a < dst ∨ dst+xs.length ≤ a) → u.mem a = st.mem a := by
  intro xs
  have len : xs.length = 3*m+2 := arcFields_length ..
  have vals : ∀ x ∈ xs, x ≤ max n W := arcFields_bound tail head weight s t hw
  obtain ⟨positions,work⟩ := fields_bounds xs (max n W) vals
  rw [len] at positions work
  have tape : τ.input.drop p = field n ++ (field m ++ (fields xs ++ (encInt B ++ suffix))) := by
    simpa only [encodeParity_fields,List.append_assoc] using input
  have pos : (p+(field n).length+(field m).length+(fields xs).length).size ≤ b := by
    apply (Nat.size_le_size ?_).trans hp
    simpa only [field_length] using Nat.add_le_add_left positions (p+(2*n.size+1)+(2*m.size+1))
  obtain ⟨u,j,read,hj,un,um,up,ud,data,out,fr⟩ :=
    graphHeader_exec (τ := τ) r st p dst n m xs (encInt B++suffix) len tape ptr dest sep fit hb
      (by have := Nat.size_le_size (le_max_left n W); omega) hm hcount (by rwa [len])
      (fun x hx => by have := Nat.size_le_size (vals x hx); omega) pos
  refine ⟨u,j,read,by omega,un,um,up,?_,ud,data,out,fr⟩
  rw [up,← List.drop_drop,← List.drop_drop,← List.drop_drop,tape,List.drop_left,List.drop_left,List.drop_left]

end DirectedHamiltonicity.Main

end HamiltonianInputFields

section LogCostRAMStridedMax

namespace TargetedSamplers.Structured

/-- Maximum of a finite prefix, using zero as the maximum of the empty prefix. -/
def prefixMax (v : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => max (prefixMax v i) (v i)

private theorem maxBody_exec {τ : Tapes} (r : Fin 8 ↪ ℕ) {s : Store} {b addr stride old val : ℕ}
    (ptr : s.mem (r 3) = addr) (step : s.mem (r 4) = stride) (acc : s.mem (r 6) = old)
    (hz : s.mem (r 7) = 0) (v : s.mem addr = val) (hw : (addr+stride).size ≤ b) (fit : s.Fits b) :
    let u := ((maxBody r).run τ s).last
    ∃ k ≤ 4, Exec τ (fun t => t.Fits b) (maxBody r).cmd s u k ∧
      u.mem (r 3) = addr+stride ∧ u.mem (r 6) = max old val ∧ u.out = s.out ∧
      ∀ a, a ≠ r 3 → a ≠ r 5 → a ≠ r 6 → u.mem a = s.mem a := by
  have eq (i j : Fin 8) : r i = r j ↔ i=j := r.injective.eq_iff
  have vw := v ▸ fit addr
  have ww : ((maxBody r).run τ s).writeWidth ≤ b := by
    by_cases h : old ≤ val <;>
      simp [maxBody,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
        Function.update_apply,eq,ptr,step,acc,hz,v,h,hw,vw]
  refine ⟨_,?_,(maxBody r).exec τ s b fit ww,?_,?_,?_,?_⟩
  all_goals first
    | (intro a h3 h5 h6
       by_cases ht : old ≤ val <;> simp [maxBody,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
         Function.update_apply,eq,ptr,acc,v,ht,h3,h5,h6])
    | (by_cases ht : old ≤ val <;>
       simp [maxBody,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
         eq,ptr,step,acc,hz,v,ht,max_def])

/-- Scan one field of fixed-size records. The output depends only on the values at the
requested offsets and all memory outside the four mutable registers is preserved. -/
theorem stridedMax_exec {τ : Tapes} (r : Fin 8 ↪ ℕ) {b : ℕ} (s : Store) (base stride count : ℕ)
    (val : ℕ → ℕ) (data : ∀ i < count, s.mem (base+i*stride) = val i) (sep : ∀ i, r i < base)
    (start : s.mem (r 0) = 0) (stop : s.mem (r 1) = count) (unit : s.mem (r 2) = 1)
    (ptr : s.mem (r 3) = base) (step : s.mem (r 4) = stride) (acc : s.mem (r 6) = 0) (hz : s.mem (r 7) = 0)
    (fit : s.Fits b) (hw : (base+count*stride).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (stridedMax r) s t j ∧ j ≤ 7*count+1 ∧
      t.mem (r 6) = prefixMax val count ∧ t.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 5 → a ≠ r 6 → t.mem a = s.mem a := by
  let state (i : ℕ) (u : Store) : Prop :=
    u.mem (r 0) = i ∧ u.mem (r 3) = base+i*stride ∧ u.mem (r 6) = prefixMax val i ∧ u.out = s.out ∧
      ∀ a, a ≠ r 0 → a ≠ r 3 → a ≠ r 5 → a ≠ r 6 → u.mem a = s.mem a
  have ne {i j : Fin 8} (h : i ≠ j) := r.injective.ne h
  have kept {i : ℕ} {u : Store} (h : state i u) (a : Fin 8) (h0 : a ≠ 0) (h3 : a ≠ 3) (h5 : a ≠ 5) (h6 : a ≠ 6) :=
    h.2.2.2.2 (r a) (ne h0) (ne h3) (ne h5) (ne h6)
  have control (i : ℕ) (_ : i ≤ count) (u : Store) (h : state i u) :
      u.mem (r 0) = 0+i ∧ u.mem (r 1) = 0+count := by
    simpa using And.intro h.1 ((kept h 1 (by decide) (by decide) (by decide) (by decide)).trans stop)
  have work (i : ℕ) (hi : i < count) (u : Store) (h : state i u) (fu : u.Fits b) :
      ∃ z k, Exec τ (fun st => st.Fits b) (maxBody r).cmd u z k ∧ k ≤ 4 ∧ z.mem (r 0) = 0+i ∧ z.mem (r 2) = 1 ∧
        state (i+1) (z.write (r 0) (0+i+1)) := by
    have outside (j : Fin 8) : base+i*stride ≠ r j := by have := sep j; omega
    have src := (h.2.2.2.2 _ (outside 0) (outside 3) (outside 5) (outside 6)).trans (data i hi)
    have addr : base+i*stride+stride = base+(i+1)*stride := by rw [Nat.succ_mul,Nat.add_assoc]
    have hbnd : base+i*stride+stride ≤ base+count*stride := addr ▸ Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
    obtain ⟨k,hk,ex,pos,mx,out,fr⟩ := maxBody_exec (τ := τ) r h.2.1
      ((kept h 4 (by decide) (by decide) (by decide) (by decide)).trans step) h.2.2.1
      ((kept h 7 (by decide) (by decide) (by decide) (by decide)).trans hz) src ((Nat.size_le_size hbnd).trans hw) fu
    let z := ((maxBody r).run τ u).last
    refine ⟨z,k,ex,hk,by simpa using (fr _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans h.1,
      (fr _ (ne (by decide)) (ne (by decide)) (ne (by decide))).trans
        ((kept h 2 (by decide) (by decide) (by decide) (by decide)).trans unit),?_,?_,?_,out.trans h.2.2.2.1,?_⟩
    · simp [Store.write]
    · simpa only [Store.write,Function.update_of_ne (ne (by decide : (3:Fin 8) ≠ 0)),addr] using pos
    · simpa only [Store.write,Function.update_of_ne (ne (by decide : (6:Fin 8) ≠ 0)),prefixMax] using mx
    · intro a h0 h3 h5 h6
      simpa [Store.write,h0] using (fr a h3 h5 h6).trans (h.2.2.2.2 a h0 h3 h5 h6)
  have initial : state 0 s := ⟨start,by simpa using ptr,acc,rfl,fun _ _ _ _ _ => rfl⟩
  obtain ⟨t,j,ex,hj,last⟩ := forRange_exec (τ := τ) (r 0) (r 1) (r 2) 0 count 4 (maxBody r).cmd state control work
    (by simpa using (stop ▸ fit (r 1))) s initial fit
  exact ⟨t,j,ex,by omega,last.2.2.1,last.2.2.2⟩

end TargetedSamplers.Structured

end LogCostRAMStridedMax

section LogCostRAMScale

namespace TargetedSamplers.Structured.Word

theorem addRepeatedly_exec {τ : Tapes} (r : Fin 5 ↪ ℕ) {b : ℕ} (n v a : ℕ) (s : Store)
    (count : s.mem (r 0) = n) (value : s.mem (r 1) = v) (acc : s.mem (r 2) = a)
    (zero : s.mem (r 3) = 0) (one : s.mem (r 4) = 1) (fit : s.Fits b) (width : (a+n*v).size ≤ b) :
    ∃ t, Exec τ (fun st => st.Fits b) (addRepeatedly r) s t (4*n+1) ∧ t.mem (r 0) = 0 ∧
      t.mem (r 2) = a+n*v ∧ t.out = s.out ∧ ∀ k, k ≠ r 0 → k ≠ r 2 → t.mem k = s.mem k := by
  have ne {i j : Fin 5} (h : i ≠ j) := r.injective.ne h
  induction n generalizing s a with
  | zero => exact ⟨s,.done (by rw [count,zero]),count,by simpa using acc,rfl,fun _ _ _ => rfl⟩
  | succ n ih =>
    let u := s.write (r 2) (a+v)
    let t := u.write (r 0) n
    have put : (Op.add (r 2) (r 2) (r 1)).eval τ s = u := by simp [Op.eval,u,acc,value]
    have total : a+v+n*v = a+(n+1)*v := by rw [Nat.succ_mul]; omega
    have w := (Nat.size_le_size (show a+v ≤ a+(n+1)*v by omega)).trans width
    have fu : u.Fits b := Store.write_fits fit _ w
    have ex : Exec τ (fun st => st.Fits b) (.op (.add (r 2) (r 2) (r 1))) s u 1 := by
      simpa only [put] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.add (r 2) (r 2) (r 1)) (by rwa [put]))
    have prior (i : Fin 5) (h : i ≠ 2) : u.mem (r i) = s.mem (r i) := by simp [u,Store.write,ne h]
    have dec : (Op.sub (r 0) (r 0) (r 4)).eval τ u = t := by
      simp [Op.eval,t,prior 0 (by decide),prior 4 (by decide),count,one]
    have wn := (Nat.size_le_size (show n ≤ n+1 by omega)).trans (count ▸ fit (r 0))
    have ft : t.Fits b := Store.write_fits fu _ wn
    have ed : Exec τ (fun st => st.Fits b) (.op (.sub (r 0) (r 0) (r 4))) u t 1 := by
      simpa only [dec] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.sub (r 0) (r 0) (r 4)) (by rwa [dec]))
    have kept (k : ℕ) (h0 : k ≠ r 0) (h2 : k ≠ r 2) : t.mem k = s.mem k := by simp [t,u,Store.write,h0,h2]
    obtain ⟨z,loop,zc,zv,out,frame⟩ := ih (a+v) t (by simp [t,Store.write]) ((kept _ (ne (by decide)) (ne (by decide))).trans value)
      (by simp [t,u,Store.write,ne (by decide : (2:Fin 5) ≠ 0)]) ((kept _ (ne (by decide)) (ne (by decide))).trans zero)
      ((kept _ (ne (by decide)) (ne (by decide))).trans one) ft (by rwa [total])
    have g : ¬s.mem (r 0) ≤ s.mem (r 3) := by rw [count,zero]; omega
    refine ⟨z,?_,zc,zv.trans total,out,fun k h0 h2 => (frame k h0 h2).trans (kept k h0 h2)⟩
    rw [show 4*(n+1)+1 = 1+(1+1)+1+(4*n+1) by omega]
    exact .again g (ex.seq ed) loop

end TargetedSamplers.Structured.Word

end LogCostRAMScale

section HamiltonianInputBound

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryRead

def weightAt {m : ℕ} (w : Fin m → ℕ) (i : ℕ) : ℕ := if h : i < m then w ⟨i,h⟩ else 0

private theorem prefixMax_le_iff (w : ℕ → ℕ) (j a : ℕ) :
    prefixMax w j ≤ a ↔ ∀ i < j, w i ≤ a := by
  induction j with
  | zero => simp [prefixMax]
  | succ j ih =>
    rw [prefixMax,max_le_iff,ih]
    constructor
    · rintro ⟨p,q⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with v|rfl
      · exact p i v
      · exact q
    · exact fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi),h j (Nat.lt_succ_self j)⟩

theorem prefixMax_fin {m : ℕ} (w : Fin m → ℕ) :
    prefixMax (weightAt w) m = Finset.univ.sup w := by
  apply le_antisymm
  · apply (prefixMax_le_iff ..).2
    intro i hi
    simpa [weightAt,hi] using (Finset.le_sup (f := w) (Finset.mem_univ (⟨i,hi⟩ : Fin m)))
  · apply Finset.sup_le
    intro i _
    simpa [weightAt,i.isLt] using (prefixMax_le_iff (weightAt w) m _).1 le_rfl i.val i.isLt

private structure MaxStart (u : Store) (m : ℕ) : Prop where
  index : u.mem 11 = 0
  count : u.mem 12 = m
  one : u.mem 13 = 1
  addr : u.mem 14 = graphBase+2
  stride : u.mem 15 = 3
  acc : u.mem 17 = 0
  zero : u.mem 18 = 0

private theorem setupMax_exec {τ : Tapes} {b m : ℕ} (s : Store) (fit : s.Fits b)
    (count : s.mem 8 = m) (width : (graphBase+2).size ≤ b) :
    let u := (setupMax.run τ s).last
    Exec τ (fun t => t.Fits b) setupMax.cmd s u 7 ∧ MaxStart u m ∧ u.out = s.out ∧
    ∀ a, (a < 11 ∨ 18 < a) → u.mem a = s.mem a := by
  
  have three := (Nat.size_le_size (by decide : 3 ≤ graphBase+2)).trans width
  have hb : 2 ≤ b := (by decide : 2 ≤ (graphBase+2).size).trans width
  have hm := count ▸ fit 8
  have w : (setupMax.run τ s).writeWidth ≤ b := by
    simp [setupMax,Structured.sequence,Fragment.run,Op.written,Op.eval,Store.write,count,hm,three,width]; omega
  refine ⟨setupMax.exec τ s b fit w,?_,rfl,?_⟩
  · constructor <;> simp [setupMax,Structured.sequence,Fragment.run,Op.eval,Store.write,count]
  · intro a h
    have ne (i : ℕ) (lo : 11 ≤ i) (hi : i ≤ 18) : a ≠ i := by omega
    simp [setupMax,Structured.sequence,Fragment.run,Op.eval,Store.write,ne 11 (by decide) (by decide),
      ne 12 (by decide) (by decide),ne 13 (by decide) (by decide),ne 14 (by decide) (by decide),
      ne 15 (by decide) (by decide),ne 17 (by decide) (by decide),ne 18 (by decide) (by decide)]

theorem computeBound_exec {τ : Tapes} {b n m : ℕ} (s : Store) (weight : Fin m → ℕ)
    (hn : s.mem 7 = n) (hm : s.mem 8 = m)
    (data : ∀ e : Fin m, s.mem (graphBase+3*e.val+2) = weight e)
    (fit : s.Fits b) (addresses : (graphBase+2+m*3).size ≤ b)
    (capWidth : ((n-1)*Finset.univ.sup weight).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) computeBound s t j ∧ j ≤ 7*m+4*(n-1)+11 ∧
      t.mem 17 = Finset.univ.sup weight ∧ t.mem 20 = (n-1)*Finset.univ.sup weight ∧ t.out = s.out ∧
      ∀ a, (a < 11 ∨ 20 < a) → t.mem a = s.mem a := by
  obtain ⟨setup,regs,out₀,frame₀⟩ := setupMax_exec (τ := τ) s fit hm
    ((Nat.size_le_size (Nat.le_add_right (graphBase+2) (m*3))).trans addresses)
  let u := (setupMax.run τ s).last
  have tab (i : ℕ) (hi : i < m) : u.mem (graphBase+2+i*3) = weightAt weight i := by
    rw [show u.mem (graphBase+2+i*3) = s.mem (graphBase+2+i*3) from frame₀ _ (.inr (by simp [graphBase]; omega)),
      show graphBase+2+i*3 = graphBase+3*i+2 by omega,data ⟨i,hi⟩]
    simp [weightAt,hi]
  obtain ⟨v,k,scan,hk,maxWord,out₁,fr₁⟩ := stridedMax_exec (τ := τ) maxRegs u (graphBase+2) 3 m
    (weightAt weight) tab (by intro i; change 11+i.val < 128+2; have := i.isLt; omega)
    regs.index regs.count regs.one regs.addr regs.stride regs.acc regs.zero (setup.post fit) addresses
  have vmax : v.mem 17 = Finset.univ.sup weight := maxWord.trans (prefixMax_fin weight)
  have keep₁ (a : ℕ) (h₁ : a ≠ 11) (h₂ : a ≠ 14) (h₃ : a ≠ 16) (h₄ : a ≠ 17) :
      v.mem a = u.mem a := fr₁ a h₁ h₂ h₃ h₄
  have vzero : v.mem 18 = 0 := (keep₁ 18 (by decide) (by decide) (by decide) (by decide)).trans regs.zero
  have vone : v.mem 13 = 1 := (keep₁ 13 (by decide) (by decide) (by decide) (by decide)).trans regs.one
  have vn : v.mem 7 = n := (keep₁ 7 (by decide) (by decide) (by decide) (by decide)).trans ((frame₀ 7 (by decide)).trans hn)
  let z := (setupFactor.run τ v).last
  have fv := scan.post (setup.post fit)
  have wsub := (Nat.size_le_size (Nat.sub_le n 1)).trans (vn ▸ fv 7)
  have wz : (setupFactor.run τ v).writeWidth ≤ b := by
    simp [setupFactor,Structured.sequence,Fragment.run,Op.written,vn,vone,wsub]
  have factor := setupFactor.exec τ v b fv wz
  have zcount : z.mem 19 = n-1 := by simp [z,setupFactor,Structured.sequence,Fragment.run,Op.eval,Store.write,vn,vone]
  have zinit : z.mem 20 = 0 := by rfl
  have keep₂ (a : ℕ) (h₁ : a ≠ 19) (h₂ : a ≠ 20) : z.mem a = v.mem a := by
    simp [z,setupFactor,Structured.sequence,Fragment.run,Op.eval,Store.write,h₁,h₂]
  obtain ⟨t,mul,_,product,out₃,fr₃⟩ := Word.addRepeatedly_exec (τ := τ) factorRegs (n-1)
    (Finset.univ.sup weight) 0 z zcount ((keep₂ 17 (by decide) (by decide)).trans vmax) zinit
    ((keep₂ 18 (by decide) (by decide)).trans vzero) ((keep₂ 13 (by decide) (by decide)).trans vone)
    (factor.post fv) (by simpa using capWidth)
  have endMax : t.mem 17 = Finset.univ.sup weight := (fr₃ 17 (by decide) (by decide)).trans
    ((keep₂ 17 (by decide) (by decide)).trans vmax)
  have nfactor : (setupFactor.run τ v).steps = 2 := rfl
  change t.mem 20 = 0+(n-1)*Finset.univ.sup weight at product
  refine ⟨t,_,setup.seq (scan.seq (factor.seq mul)),by omega,endMax,product.trans (Nat.zero_add _),
    out₃.trans (out₁.trans out₀),?_⟩
  intro a ha
  have h19 : a ≠ 19 := by omega
  have h20 : a ≠ 20 := by omega
  exact (fr₃ a h19 h20).trans ((keep₂ a h19 h20).trans ((keep₁ a (by omega) (by omega) (by omega) (by omega)).trans
    (frame₀ a (by omega))))

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianInputBound

section HamiltonianRAMInput

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.BinaryRead

def prefixLimit (n m W : ℕ) : ℕ :=
  (2*n.size+1)+(2*m.size+1)+(3*m+2)*(2*(max n W).size+1)

/-- B and the length of the coin tape are absent from the parser's resource bounds. -/
def parserWidth (n m W : ℕ) : ℕ :=
  160 + prefixLimit n m W + 3*m + (max n W).size + m.size + 3*((n-1)*W).size

def parserSteps (n m W : ℕ) : ℕ :=
  10*n.size+10*m.size+(3*m+2)*(10*(max n W).size+12)+7*m+4*(n-1)+11*((n-1)*W).size+54

private theorem size_self (x : ℕ) : x.size ≤ x := Nat.size_le.mpr x.lt_two_pow_self

set_option maxHeartbeats 700000 in
theorem readInstance_exec {n m W : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ) (s t : Fin n)
    (hw : ∀ e, weight e ≤ W) (B : ℤ) (coins : List Bool) :
    let τ := runTapes (encodeParityInstance n m tail head weight s t B) coins
    ∃ u j, Exec τ (fun v => v.Fits (parserWidth n m W)) readInstance initial u j ∧
      j ≤ parserSteps n m W ∧ Parsed tail head weight s t B u := by
  intro τ
  let b := parserWidth n m W
  let xs := arcFields tail head weight s t
  let cap := (n-1)*Finset.univ.sup weight
  have maxW : Finset.univ.sup weight ≤ W := Finset.sup_le fun e _ => hw e
  have capW : cap.size ≤ ((n-1)*W).size := Nat.size_le_size (Nat.mul_le_mul_left _ maxW)
  have len : xs.length = 3*m+2 := arcFields_length .. 
  have f0 : initial.Fits b := by intro a; simp [initial]
  have hb : 2 ≤ b := by dsimp [b,parserWidth]; omega
  let start := initial.write 10 graphBase
  have fb : start.Fits b := Store.write_fits f0 10 (by dsimp [b,parserWidth,graphBase]; have := size_self 128; omega)
  have init : Exec τ (fun v => v.Fits b) (.op (.const 10 graphBase)) initial start 1 := .op _ _ fb
  have sep (i : Fin 11) : headerRegs i < graphBase := by change i.val < 128; have := i.isLt; omega
  have countWidth : (3*m+2).size ≤ b := by have := size_self (3*m+2); dsimp [b,parserWidth]; omega
  have addressWidth : (graphBase+(3*m+2)).size ≤ b := by
    have := size_self (graphBase+(3*m+2)); dsimp [b,parserWidth,graphBase] at *; omega
  have prefixWidth : (prefixLimit n m W).size ≤ b := by
    have := size_self (prefixLimit n m W); dsimp [b,parserWidth]; omega
  obtain ⟨u,i,loadGraph,wi,nWord,mWord,cursor,remaining,endWord,table,out₁,free₁⟩ :=
    read_graph_ram tail head weight s t hw B headerRegs (τ := τ) start 0 graphBase []
      (by simp [τ,runTapes]) (by rfl) (by rfl) sep fb hb (by dsimp [b,parserWidth]; omega)
      (by dsimp [b,parserWidth]; omega) countWidth addressWidth (by simpa only [prefixLimit,Nat.zero_add] using prefixWidth)
  have weights (e : Fin m) : u.mem (graphBase+3*e.val+2) = weight e := by
    have hi : 3*e.val+2 < xs.length := by have := e.isLt; omega
    have loc : xs[3*e.val+2]? = some (weight e) := arcFields_weight tail head weight s t e
    rw [List.getElem?_eq_getElem hi] at loc
    rw [Nat.add_assoc,table _ hi,Option.some.inj loc]
  obtain ⟨v,k,findCap,wk,maxWord,capWord,out₂,free₂⟩ := computeBound_exec (τ := τ) u weight nWord mWord
    weights (loadGraph.post fb) (by rwa [show graphBase+2+m*3 = graphBase+(3*m+2) by omega])
    (by change cap.size ≤ b; dsimp [b,parserWidth]; omega)
  have pos : v.mem 0 = u.mem 0 := free₂ 0 (by decide)
  have ptr : u.mem 0 ≤ prefixLimit n m W := by
    have sz := (fields_bounds xs (max n W) (arcFields_bound tail head weight s t hw)).1
    change u.mem 0 = 0+(field n).length+(field m).length+(fields xs).length at cursor
    rw [len] at sz
    rw [cursor,field_length,field_length]
    dsimp [prefixLimit]; omega
  have digits (i : Fin 7) : digitRegs headerRegs i < 7 := i.isLt
  have far (a : ℕ) (ha : 7 ≤ a) (i : Fin 7) : a ≠ digitRegs headerRegs i := by have := digits i; omega
  have pwidth : (u.mem 0+1+2*cap.size).size ≤ b := by
    have := size_self (u.mem 0+1+2*cap.size)
    dsimp [b,parserWidth]; omega
  obtain ⟨z,j,readB,wj,ok,value,out₃,free₃⟩ := read_target_ram (τ := τ) (digitRegs headerRegs) 20 9
    (by decide) (far 20 (by decide)) (far 9 (by decide)) v (u.mem 0) cap B [] capWord pos
    (findCap.post (loadGraph.post fb)) hb (by dsimp [b,parserWidth]; omega) pwidth remaining
  have keep (a : ℕ) (ha : 7 ≤ a) (h9 : a ≠ 9) : z.mem a = v.mem a := free₃ a h9 (far a ha)
  have heap (a : ℕ) (ha : 21 ≤ a) : z.mem a = u.mem a :=
    (keep a (by omega) (by omega)).trans (free₂ a (by omega))
  refine ⟨z,_,init.seq (loadGraph.seq (findCap.seq readB)),?_,?_⟩
  · dsimp [parserSteps]; omega
  · refine ⟨(keep 7 (by decide) (by decide)).trans ((free₂ 7 (by decide)).trans nWord),
      (keep 8 (by decide) (by decide)).trans ((free₂ 8 (by decide)).trans mWord),
      (keep 17 (by decide) (by decide)).trans maxWord,(keep 20 (by decide) (by decide)).trans capWord,
      ok,value,?_,?_,?_,out₃.trans (out₂.trans out₁)⟩
    · exact (keep 10 (by decide) (by decide)).trans ((free₂ 10 (by decide)).trans (endWord.trans (congrArg (graphBase+·) len)))
    · intro i hi
      exact (heap _ (by dsimp [graphBase]; omega)).trans (table i hi)
    · intro a ha beyond
      have clear (i : Fin 11) : a ≠ headerRegs i := by change a ≠ i.val; have := i.isLt; omega
      have outside : a < graphBase ∨ graphBase+xs.length ≤ a := by rwa [len]
      rw [heap a ha,free₁ a clear outside]
      simp [start,initial,Store.write,show a ≠ 10 by omega]

/-- One polynomial simultaneously bounds work and register widths for the parser. -/
theorem parser_polynomial (n m W : ℕ) :
    let N := n+m+W+1
    parserWidth n m W ≤ 256*(N+1)^2 ∧ parserSteps n m W ≤ 256*(N+1)^2 := by
  intro N
  have ns : n.size ≤ N := (size_self n).trans (by dsimp [N]; omega)
  have ms : m.size ≤ N := (size_self m).trans (by dsimp [N]; omega)
  have mw : (max n W).size ≤ N := (size_self _).trans (by dsimp [N]; omega)
  have mn : m ≤ N := by dsimp [N]; omega
  have nn : n-1 ≤ N := by dsimp [N]; omega
  have ww : W ≤ N := by dsimp [N]; omega
  have cap := (size_self ((n-1)*W)).trans (Nat.mul_le_mul nn ww)
  have r := Nat.mul_le_mul (by omega : 3*m+2 ≤ 3*N+2) (by omega : 2*(max n W).size+1 ≤ 2*N+1)
  have q := Nat.mul_le_mul (by omega : 3*m+2 ≤ 3*N+2) (by omega : 10*(max n W).size+12 ≤ 10*N+12)
  dsimp [parserWidth,parserSteps,prefixLimit]
  constructor <;> nlinarith only [ns,ms,mw,mn,nn,cap,r,q,Nat.zero_le (N*N),Nat.zero_le N]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMInput

section HamiltonianParitySampling

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

omit [DecidableEq V] [DecidableEq E] in
theorem samplingDegree_le {d : ℕ} (hd : 1 ≤ d) (hw : ∀ v, (H.incomingWeights w v).card ≤ d) :
    H.samplingDegree w ≤ d := max_le hd (Finset.sup_le fun v _ => hw v)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParitySampling

section HamiltonianRAMSchedule

namespace DirectedHamiltonicity.Main.Multidigraph

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

/-- The exponential-valued trial count is constructed in polynomial preliminary time. -/
theorem schedule_polynomial (n d : ℕ) :
    let S := n+d+2
    scheduleWidth n d ≤ 18*S^2 ∧ scheduleSteps n d ≤ 40000*S^5 := by
  intro S
  let w := scheduleWidth n d
  have pos : 1 ≤ S := by dsimp [S]; omega
  have ns : n ≤ S := by dsimp [S]; omega
  have ds : d+1 ≤ S := by dsimp [S]; omega
  have qs : n-2 ≤ S := by omega
  have ss : S ≤ S^2 := by simpa [pow_two] using Nat.mul_le_mul_left S pos
  have ss' : 1 ≤ S^2 := pos.trans ss
  have deg := Nat.mul_le_mul ds qs
  have word : w ≤ 18*S^2 := by
    dsimp [w,scheduleWidth]
    have joint : n+d ≤ S := by dsimp [S]; omega
    nlinarith only [deg,joint,ss,ss']
  have quad := Nat.mul_le_mul word (show 5*w+9 ≤ 99*S^2 by omega)
  have fourth : 1 ≤ S^4 := Nat.succ_le_of_lt (pow_pos pos 4)
  have per : w*(5*w+9)+15 ≤ 1800*S^4 := by nlinarith only [quad,fourth]
  have calls : d+2*(n-2)+15 ≤ 18*S := by omega
  refine ⟨word,(Nat.mul_le_mul calls per).trans ?_⟩
  nlinarith only [Nat.zero_le (S^5)]

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRAMSchedule

section HamiltonianRAMGuard

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured

private theorem guardZero {n m : ℕ} {tail head : Fin m → Fin n} {weight : Fin m → ℕ} {s t : Fin n}
    {B : ℤ} {u : Store} (h : Parsed tail head weight s t B u) : u.mem 21 = 0 :=
  h.free 21 le_rfl (.inl (by decide))

/-- On every coin tape a target outside the feasible range returns false in polynomial
bit cost, including decoding the graph, branching, output, and halting. The constant
static instruction width can depend on the fixed body. -/
theorem onValid_rejects (body : Cmd) {n m W : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ)
    (s t : Fin n) (hw : ∀ e, weight e ≤ W) (B : ℤ)
    (bad : B < 0 ∨ (((n-1)*Finset.univ.sup weight : ℕ) : ℤ) < B) (coins : List Bool) :
    let τ := runTapes (encodeParityInstance n m tail head weight s t B) coins
    let P := (onValid body).program
    let K := 256*(n+m+W+1+1)^2
    ∃ cost, P.RunsIn τ cost (some [false]) ∧ cost ≤ (K+4)*(6*max K (staticWidth P)+2) := by
  intro τ P K
  obtain ⟨u,j,parse,work,h⟩ := readInstance_exec tail head weight s t hw B coins
  have zero := guardZero h
  have no : ¬u.mem 9 ≤ u.mem 21 := by rw [zero,Nat.le_zero,h.valid]; omega
  have fit : initial.Fits (parserWidth n m W) := by intro a; simp [initial]
  let z := (Op.output 21).eval τ u
  have ex : Exec τ (fun v => v.Fits (parserWidth n m W)) (.op (.output 21)) u z 1 :=
    .op _ _ (parse.post fit)
  have run : Exec τ (fun v => v.Fits (parserWidth n m W)) (onValid body) initial z (j+(1+1+1)) :=
    parse.seq (.no no ex)
  have out : z.out = [false] := by simp [z,Op.eval,h.output,zero]
  obtain ⟨bw,bj⟩ := parser_polynomial n m W
  let cost := (j+(1+1+1)+1)*(6*max (parserWidth n m W) (staticWidth P)+2)
  refine ⟨cost,?_,Nat.mul_le_mul (by dsimp [K]; omega) (Nat.add_le_add_right (Nat.mul_le_mul_left 6
    (max_le_max_right (staticWidth P) bw)) 2)⟩
  simpa only [out] using run.runsIn

/-- For a valid target a proof of the body can start from the decoded table, at the
exact store and with the step count of the preceding parser. -/
theorem onValid_accepts {body : Cmd} {n m W : ℕ} (tail head : Fin m → Fin n) (weight : Fin m → ℕ)
    (s t : Fin n) (hw : ∀ e, weight e ≤ W) (B : ℤ)
    (good : 0 ≤ B ∧ B ≤ (((n-1)*Finset.univ.sup weight : ℕ) : ℤ)) (coins : List Bool)
    (width : ℕ) (hwid : parserWidth n m W ≤ width) :
    let τ := runTapes (encodeParityInstance n m tail head weight s t B) coins
    ∃ u j, Parsed tail head weight s t B u ∧ u.Fits width ∧ j ≤ parserSteps n m W ∧
      ∀ z k, Exec τ (fun v => v.Fits width) body u z k →
        Exec τ (fun v => v.Fits width) (onValid body) initial z (j+1+k) := by
  intro τ
  obtain ⟨u,j,parse,work,h⟩ := readInstance_exec tail head weight s t hw B coins
  have raised {v : Store} (hv : v.Fits (parserWidth n m W)) : v.Fits width := fun a => (hv a).trans hwid
  have path := parse.weakenInv (fun _ => raised)
  refine ⟨u,j,h,raised (parse.post (by intro a; simp [initial])),work,?_⟩
  intro z k run
  have ok : u.mem 9 ≤ u.mem 21 := by rw [h.valid.mpr good,guardZero h]
  simpa only [τ,onValid,Nat.add_assoc] using path.seq (Exec.yes (n := .op (.output 21)) ok run)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMGuard

section HamiltonianRAMPreprocess

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Word

open Multidigraph Classical

/-- Explicit preprocessing bounds in the same parameters as the posted proposition. -/
theorem preprocess_polynomial (n m W d : ℕ) (hd : d ≤ W+1) :
    let N := n+m+W+3
    scheduleWidth n d ≤ 256*N^2 ∧ parserWidth n m W ≤ 256*N^2 ∧
      parserSteps n m W+1+preprocessWork n m W d ≤ 50000*N^5 := by
  intro N
  have hn : n ≤ N := by dsimp [N]; omega
  have hm : m ≤ N := by dsimp [N]; omega
  have hw : W+1 ≤ N := by dsimp [N]; omega
  have pos : 1 ≤ N := by dsimp [N]; omega
  have s := schedule_polynomial n d
  have parse := parser_polynomial n m W
  have e : n+d+2 ≤ N := by dsimp [N]; omega
  have short : n+m+W+1+1 ≤ N := by dsimp [N]; omega
  have a := Nat.pow_le_pow_left e 2
  have c := Nat.pow_le_pow_left e 5
  have t := Nat.pow_le_pow_left short 2
  have m₁ := Nat.mul_le_mul hn (show 18*m+20 ≤ 38*N by omega)
  have sq : 1 ≤ N^2 := Nat.succ_le_of_lt (pow_pos pos 2)
  have m₂ := Nat.mul_le_mul hw (show n*(18*m+20)+8 ≤ 46*N^2 by nlinarith only [m₁,sq])
  have cube : 1 ≤ N^3 := Nat.succ_le_of_lt (pow_pos pos 3)
  have m₃ := Nat.mul_le_mul hn (show (W+1)*(n*(18*m+20)+8)+8 ≤ 54*N^3 by nlinarith only [m₂,cube])
  have s₂ : N^2 ≤ N^5 := Nat.pow_le_pow_right pos (by decide)
  have s₄ : N^4 ≤ N^5 := Nat.pow_le_pow_right pos (by decide)
  have large : 1 ≤ N^5 := pos.trans (by simpa using Nat.pow_le_pow_right pos (by decide : 1 ≤ 5))
  change scheduleWidth n d ≤ 18*(n+d+2)^2 ∧ scheduleSteps n d ≤ 40000*(n+d+2)^5 at s
  obtain ⟨sw,ss⟩ := s
  obtain ⟨pw,ps⟩ := parse
  refine ⟨by omega,by omega,?_⟩
  dsimp [preprocessWork]; nlinarith only [ss,ps,c,t,s₂,s₄,large,m₃]

/-- From the published tape encoding, enter an arbitrary trial body with the correct target
and trial count. The preceding command is the same for every graph and every random tape. -/
theorem enterTrials {body : Cmd} {n m W : ℕ} (tail head : Fin m → Fin n) (w : Fin m → ℕ)
    (hw : ∀ e, w e ≤ W) (s t : Fin n) (B : ℤ)
    (good : 0 ≤ B ∧ B ≤ (((n-1)*Finset.univ.sup w : ℕ):ℤ)) (coins : List Bool) :
    let V := Finset.univ.sup w
    let cover : ∀ e, w e ≤ V := fun e => Finset.le_sup (Finset.mem_univ e)
    let H : Multidigraph (Fin n) (Fin m) := ⟨tail,head⟩
    let G := Multidigraph.normalizedGraph H w s t cover
    let p := Multidigraph.normalizedWeight H w s t cover
    let d := Multidigraph.samplingDegree G p
    let τ := runTapes (encodeParityInstance n m tail head w s t B) coins
    let N := n+m+W+3
    ∀ width : ℕ, 256*N^2 ≤ width →
    ∃ a j, a.Fits width ∧ j ≤ 50000*N^5 ∧ GraphView (W := V) tail head w s t graphBase a ∧
      a.mem 52 = d ∧ a.mem 53 = B.toNat ∧ a.mem 54 = samplingBlockSize n d*(n+4) ∧ a.out = [] ∧
      (∀ addr ≥ graphBase+(3*m+2), a.mem addr=0) ∧
      ∀ z k, Exec τ (fun v => v.Fits width) body a z k →
        Exec τ (fun v => v.Fits width) (onValid (.seq preprocess body)) initial z (j+k) := by
  intro V cover H G p d τ N width wider
  have maxLe : V ≤ W := Finset.sup_le fun e _ => hw e
  have dV : d ≤ V+1 := by
    apply Multidigraph.samplingDegree_le G p (by omega)
    intro v
    have sub : Multidigraph.incomingWeights G p v ⊆ Finset.range (V+1) := by
      intro i hi
      obtain ⟨a,_,eq⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (eq ▸ a.1.2.2.isLt)
    simpa using Finset.card_le_card sub
  have hd : d ≤ W+1 := by omega
  obtain ⟨sw,pw,cost⟩ := preprocess_polynomial n m W d hd
  obtain ⟨u,i,parsed,fu,read,guard⟩ := onValid_accepts (body := .seq preprocess body) tail head w s t hw B good coins width (pw.trans wider)
  have room : (V+1).size ≤ width := by
    have ne : 1 ≤ N := by dsimp [N]; omega
    have le : V+1 ≤ N := by dsimp [N]; omega
    have sq : N ≤ N^2 := by simpa [pow_two] using Nat.mul_le_mul_left N ne
    have size := Nat.size_le.mpr (V+1).lt_two_pow_self
    omega
  obtain ⟨a,j,init,used,view,degree,target,trials,out,heap⟩ := preprocess_exec (τ := τ) u parsed fu room (sw.trans wider)
  have upper : preprocessWork n m V d ≤ preprocessWork n m W d := by
    dsimp [preprocessWork]; gcongr
  change j ≤ preprocessWork n m V d at used
  change parserSteps n m W+1+preprocessWork n m W d ≤ 50000*N^5 at cost
  refine ⟨a,i+1+j,init.post fu,(Nat.add_le_add (Nat.add_le_add_right read 1) (used.trans upper)).trans cost,
    view,degree,target.trans (parsed.target good.1 good.2),
    trials,out.trans parsed.output,heap,?_⟩
  intro z k next
  simpa only [Nat.add_assoc] using guard z (j+k) (init.seq next)

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMPreprocess

section HamiltonianParityInput

namespace DirectedHamiltonicity.Main

theorem readTarget_encInt (cap : ℕ) (z : ℤ) (suffix : List Bool) :
    readTarget cap (encInt z ++ suffix) =
      if 0 ≤ z ∧ z ≤ (cap : ℤ) then some z.toNat else none := by
  cases z with
  | ofNat n =>
    have hsign : ¬((n : ℤ) < 0) := not_lt.mpr (Int.natCast_nonneg n)
    simpa [Int.ofNat_eq_natCast, readTarget, encInt, encNat, hsign, List.append_assoc] using
      BoundedBinaryInput.readAtMost_encoded cap n suffix
  | negSucc n => simp [readTarget, encInt]

end DirectedHamiltonicity.Main

end HamiltonianParityInput

section HamiltonianRAMBodyReduction

namespace DirectedHamiltonicity.Main.InputRAM

open TargetedSamplers TargetedSamplers.Structured Multidigraph Classical

/-- The fixed polynomial from a subroutine can be converted to the monomial used by the public statement. -/
theorem eval_monomial_bound (p : Polynomial ℕ) :
    ∃ c d : ℕ, ∀ x : ℕ, 1 ≤ x → p.eval x ≤ c*x^d := by
  induction p using Polynomial.induction_on' with
  | monomial d c =>
    exact ⟨c,d,fun x _ => by simp⟩
  | add p r hp hr =>
    obtain ⟨a,k,h⟩ := hp
    obtain ⟨c,d,g⟩ := hr
    refine ⟨a+c,max k d,fun x hx => ?_⟩
    rw [Polynomial.eval_add,Nat.add_mul]
    exact Nat.add_le_add ((h x hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (le_max_left ..))))
      ((g x hx).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (le_max_right ..))))

theorem inputEstimator_outside {n m : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ)
    (s t : Fin n) (B : ℤ) (coins : List Bool) (bad : ¬(0 ≤ B ∧ B ≤ (((n-1)*inputMaxWeight w : ℕ):ℤ))) :
    H.inputEstimator w s t (encInt B) coins=false := by
  have reject : readTarget ((n-1)*inputMaxWeight w) (encInt B)=none := by
    simpa only [List.append_nil,if_neg bad] using readTarget_encInt ((n-1)*inputMaxWeight w) B []
  simp [inputEstimator,streamedEstimate,reject]

end DirectedHamiltonicity.Main.InputRAM

end HamiltonianRAMBodyReduction

section
open DirectedHamiltonicity DirectedHamiltonicity.Main DirectedHamiltonicity.Main.InputRAM
open TargetedSamplers TargetedSamplers.Structured Multidigraph Classical

theorem solution (body : Cmd) (required work : Polynomial ℕ) (run : ValidBodyRuns body required work) :
    ∃ A k : ℕ, BoundedInputRuns (onValid (.seq preprocess body)).program A k := by
  let P := (onValid (.seq preprocess body)).program
  let x : Polynomial ℕ := Polynomial.X
  let width : Polynomial ℕ := required+256*(x+2)^2+x
  let measure : Polynomial ℕ := (50000*(x+2)^5+work.comp width+256*(x+2)^2+5)*
    (6*(width+Polynomial.C (staticWidth P))+2)
  obtain ⟨A,k,major⟩ := eval_monomial_bound measure
  refine ⟨A,k,?_⟩
  intro n m W tail head w hw s t distinct B coins H cover G p M
  let S := n+m+W+1
  let N := S+2
  let b := width.eval S
  have size : b=required.eval S+256*N^2+S := by simp [b,width,x,N]
  have grow : 256*N^2 ≤ b := by omega
  have poly : measure.eval S=(50000*N^5+work.eval b+256*N^2+5)*(6*(b+staticWidth P)+2) := by
    simp only [measure,x,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_C,
      Polynomial.eval_ofNat,Polynomial.eval_comp,Polynomial.eval_X]
    rfl
  have finish (cost : ℕ) (h : cost ≤ (M+1)*measure.eval S) : cost ≤ (M+1)*A*S^k := by
    rw [Nat.mul_assoc]
    exact h.trans (Nat.mul_le_mul_left _ (major S (by dsimp [S];omega)))
  by_cases good : 0 ≤ B ∧ B ≤ (((n-1)*inputMaxWeight w : ℕ):ℤ)
  · obtain ⟨u,j,fu,first,view,degree,target,trials,out,heap,join⟩ :=
      enterTrials (body := body) tail head w hw s t B good coins b (by simpa [N,S,Nat.add_assoc] using grow)
    obtain ⟨z,l,exec,last,answer⟩ := run n m W tail head w hw s t distinct B coins good u b
      (by change required.eval S ≤ b;omega) fu view degree target trials out heap
    have path := (join z l exec).runsIn
    rw [answer] at path
    refine ⟨_,path,finish _ ?_⟩
    change (j+l+1)*(6*max b (staticWidth P)+2) ≤ (M+1)*measure.eval S
    change j ≤ 50000*N^5 at first
    change l ≤ (M+1)*work.eval b at last
    rw [poly,← Nat.mul_assoc]
    apply Nat.mul_le_mul _ (by omega)
    have bnd := Nat.mul_le_mul_right (50000*N^5+256*N^2+5) (Nat.le_add_left 1 M)
    simp only [Nat.one_mul] at bnd
    calc
      j+l+1 ≤ (M+1)*(50000*N^5+256*N^2+5)+(M+1)*work.eval b := by omega
      _ = _ := by ring
  · obtain ⟨cost,ram,limit⟩ := onValid_rejects (.seq preprocess body) tail head w s t hw B (by
      change B < 0 ∨ (((n-1)*inputMaxWeight w : ℕ):ℤ) < B;omega) coins
    have answer := inputEstimator_outside H w s t B coins good
    refine ⟨cost,by simpa only [answer] using ram,finish _ ?_⟩
    let K := 256*(S+1)^2
    change cost ≤ (K+4)*(6*max K (staticWidth P)+2) at limit
    have le : K ≤ 256*N^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [N];omega) _)
    have cheap : cost ≤ measure.eval S := by
      rw [poly]
      exact limit.trans (Nat.mul_le_mul (by omega) (by omega))
    exact cheap.trans (by simpa using Nat.mul_le_mul_right (measure.eval S) (Nat.le_add_left 1 M))
end
