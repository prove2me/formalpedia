-- Prove2me | solution 1 for FasterWCTFPTAS.Main.Supplement.theorem_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:18:11.725468+00:00
-- url     : https://prove2.me/submissions/70463052-87e4-4e3b-bc60-c6732563d256
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FasterWCTFPTAS_Main_Supplement_SchedulingPrograms
import Theorems.Thm_FasterWCTFPTAS_Main_Supplement_corollary_A_7
import Theorems.Thm_FasterWCTFPTAS_Main_Supplement_lemma_B_1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace FasterWCTFPTAS.Main.Supplement
open Machine SmaleNinth

noncomputable def coreExec (ins : RAMInstr) (s : RAMConfig) : RAMConfig :=
  match ins with
    | .const dst c => ⟨s.pc + 1, Function.update s.regs dst c, s.ptrs, s.mem⟩
    | .add dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i + s.regs j), s.ptrs, s.mem⟩
    | .sub dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i - s.regs j), s.ptrs, s.mem⟩
    | .mul dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i * s.regs j), s.ptrs, s.mem⟩
    | .div dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i / s.regs j), s.ptrs, s.mem⟩
    | .load dst q => ⟨s.pc + 1, Function.update s.regs dst (s.mem (s.ptrs q)), s.ptrs, s.mem⟩
    | .store q i => ⟨s.pc + 1, s.regs, s.ptrs, Function.update s.mem (s.ptrs q) (s.regs i)⟩
    | .pset q c => ⟨s.pc + 1, s.regs, Function.update s.ptrs q c, s.mem⟩
    | .pcopy q q' => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q'), s.mem⟩
    | .pinc q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q + 1), s.mem⟩
    | .pdec q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q - 1), s.mem⟩
    | .jle i target => if s.regs i ≤ 0 then ⟨target, s.regs, s.ptrs, s.mem⟩ else
        ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
    | .pjle q q' target => if s.ptrs q ≤ s.ptrs q' then ⟨target, s.regs, s.ptrs, s.mem⟩ else
        ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
    | .accept => s
    | .reject => s

lemma RAMStep_eq (R : RAMProgram) (s : RAMConfig) (ins : RAMInstr) (h : R[s.pc]? = some ins) :
    RAMStep R s = coreExec ins s := by
  unfold RAMStep; rw [h]; cases ins <;> rfl

lemma step_halted (P : Program) (s : State) (h : s.halted = true) : step P s = s := by
  simp [step, h]

lemma step_none (P : Program) (s : State) (hh : s.halted = false) (h : P[s.core.pc]? = none) :
    step P s = { s with work := s.work + 1 } := by
  simp [step, hh, h]

lemma step_core (P : Program) (s : State) (i : RAMInstr) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (.core i)) :
    step P s = ⟨coreExec i s.core, false, s.work + 1, s.inputLength⟩ := by
  have h2 : (coreProgram P)[s.core.pc]? = some i := by
    simp [coreProgram, h]
  simp [step, hh, h, RAMStep_eq _ _ _ h2]

lemma step_padd (P : Program) (s : State) (d a b : ℕ) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (.padd d a b)) :
    step P s = ⟨⟨s.core.pc + 1, s.core.regs,
      Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b), s.core.mem⟩,
      false, s.work + 1, s.inputLength⟩ := by
  simp [step, hh, h]

lemma step_psub (P : Program) (s : State) (d a b : ℕ) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (.psub d a b)) :
    step P s = ⟨⟨s.core.pc + 1, s.core.regs,
      Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b), s.core.mem⟩,
      false, s.work + 1, s.inputLength⟩ := by
  simp [step, hh, h]

lemma step_ofPtr (P : Program) (s : State) (d a : ℕ) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (.ofPtr d a)) :
    step P s = ⟨⟨s.core.pc + 1,
      Function.update s.core.regs d (s.core.ptrs a : ℝ), s.core.ptrs, s.core.mem⟩,
      false, s.work + 1, s.inputLength⟩ := by
  simp [step, hh, h]

lemma step_floor_pass (P : Program) (s : State) (d a K : ℕ) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (.floorPtr d a K))
    (hg : |⌊s.core.regs a⌋| ≤ (K : ℤ) * ((s.work : ℤ) + (s.inputLength : ℤ) + 1)) :
    step P s = ⟨⟨s.core.pc + 1, s.core.regs,
      Function.update s.core.ptrs d ⌊s.core.regs a⌋, s.core.mem⟩,
      false, s.work + 1, s.inputLength⟩ := by
  simp [step, hh, h, hg]

lemma step_floor_fail (P : Program) (s : State) (d a K : ℕ) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (.floorPtr d a K))
    (hg : ¬ |⌊s.core.regs a⌋| ≤ (K : ℤ) * ((s.work : ℤ) + (s.inputLength : ℤ) + 1)) :
    step P s = { s with work := s.work + 1 } := by
  simp [step, hh, h, hg]

lemma step_halt (P : Program) (s : State) (hh : s.halted = false)
    (h : P[s.core.pc]? = some .halt) :
    step P s = ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, true, s.work + 1, s.inputLength⟩ := by
  simp [step, hh, h]


def nop (sp : ℕ) : Instr := .core (.pcopy sp sp)

/-- Relocated block of an instruction: registers `i ↦ 3i+b`, memory `z ↦ 2z+c`,
code `pc ↦ base + 3pc`, `halt ↦ jump to cont`, `sp` scratch pointer. -/
def tr (b c base cont sp : ℕ) : Instr → Instr × Instr × Instr
  | .core (.const d v) => (nop sp, nop sp, .core (.const (3 * d + b) v))
  | .core (.add d i j) => (nop sp, nop sp, .core (.add (3 * d + b) (3 * i + b) (3 * j + b)))
  | .core (.sub d i j) => (nop sp, nop sp, .core (.sub (3 * d + b) (3 * i + b) (3 * j + b)))
  | .core (.mul d i j) => (nop sp, nop sp, .core (.mul (3 * d + b) (3 * i + b) (3 * j + b)))
  | .core (.div d i j) => (nop sp, nop sp, .core (.div (3 * d + b) (3 * i + b) (3 * j + b)))
  | .core (.load d q) => (.padd sp (3 * q + b) (3 * q + b),
      (if c = 1 then .core (.pinc sp) else nop sp), .core (.load (3 * d + b) sp))
  | .core (.store q i) => (.padd sp (3 * q + b) (3 * q + b),
      (if c = 1 then .core (.pinc sp) else nop sp), .core (.store sp (3 * i + b)))
  | .core (.pset q v) => (nop sp, nop sp, .core (.pset (3 * q + b) v))
  | .core (.pcopy q q') => (nop sp, nop sp, .core (.pcopy (3 * q + b) (3 * q' + b)))
  | .core (.pinc q) => (nop sp, nop sp, .core (.pinc (3 * q + b)))
  | .core (.pdec q) => (nop sp, nop sp, .core (.pdec (3 * q + b)))
  | .core (.jle i t) => (nop sp, nop sp, .core (.jle (3 * i + b) (base + 3 * t)))
  | .core (.pjle q q' t) => (nop sp, nop sp, .core (.pjle (3 * q + b) (3 * q' + b) (base + 3 * t)))
  | .core .accept => (nop sp, nop sp, nop sp)
  | .core .reject => (nop sp, nop sp, nop sp)
  | .padd d x y => (nop sp, nop sp, .padd (3 * d + b) (3 * x + b) (3 * y + b))
  | .psub d x y => (nop sp, nop sp, .psub (3 * d + b) (3 * x + b) (3 * y + b))
  | .ofPtr d x => (nop sp, nop sp, .ofPtr (3 * d + b) (3 * x + b))
  | .floorPtr d x K => (.floorPtr (3 * d + b) (3 * x + b) K, nop sp, nop sp)
  | .halt => (nop sp, nop sp, .core (.pjle sp sp cont))

def Embeds (R Q : Program) (b c base cont sp : ℕ) : Prop :=
  ∀ i ins, Q[i]? = some ins →
    R[base + 3 * i]? = some (tr b c base cont sp ins).1 ∧
    R[base + 3 * i + 1]? = some (tr b c base cont sp ins).2.1 ∧
    R[base + 3 * i + 2]? = some (tr b c base cont sp ins).2.2

structure CRel (b c sp : ℕ) (c0 t s : RAMConfig) : Prop where
  regs : ∀ i, t.regs (3 * i + b) = s.regs i
  ptrs : ∀ i, t.ptrs (3 * i + b) = s.ptrs i
  mem : ∀ z : ℤ, t.mem (2 * z + c) = s.mem z
  fregs : ∀ i, i % 3 ≠ b → t.regs i = c0.regs i
  fptrs : ∀ i, i % 3 ≠ b → i ≠ sp → t.ptrs i = c0.ptrs i
  fmem : ∀ y : ℤ, y % 2 ≠ c → t.mem y = c0.mem y

def Good (b c sp : ℕ) (t0 t s : State) : Prop :=
  t.halted = false ∧ t.inputLength = t0.inputLength ∧ CRel b c sp t0.core t.core s.core

def TimeOK (t0 t s : State) : Prop :=
  t.work + t.inputLength ≤ t0.work + t0.inputLength + 3 * (s.work + s.inputLength)

lemma CRel_pc {b c sp : ℕ} {c0 t s : RAMConfig} (h : CRel b c sp c0 t s) (p1 p2 : ℕ) :
    CRel b c sp c0 ⟨p1, t.regs, t.ptrs, t.mem⟩ ⟨p2, s.regs, s.ptrs, s.mem⟩ :=
  ⟨h.regs, h.ptrs, h.mem, h.fregs, h.fptrs, h.fmem⟩

lemma CRel_regs {b c sp : ℕ} {c0 t s : RAMConfig} (h : CRel b c sp c0 t s) (hb : b < 3) (p1 p2 d : ℕ) (v : ℝ) :
    CRel b c sp c0 ⟨p1, Function.update t.regs (3 * d + b) v, t.ptrs, t.mem⟩
      ⟨p2, Function.update s.regs d v, s.ptrs, s.mem⟩ := by
  refine ⟨fun i => ?_, h.ptrs, h.mem, fun i hi => ?_, h.fptrs, h.fmem⟩
  · by_cases hid : i = d
    · subst hid; simp
    · have : 3 * i + b ≠ 3 * d + b := by omega
      simp [Function.update_of_ne this, Function.update_of_ne hid, h.regs]
  · have : i ≠ 3 * d + b := by omega
    simp [Function.update_of_ne this, h.fregs i hi]

lemma CRel_ptrs {b c sp : ℕ} {c0 t s : RAMConfig} (h : CRel b c sp c0 t s) (hb : b < 3) (p1 p2 d : ℕ) (v : ℤ) :
    CRel b c sp c0 ⟨p1, t.regs, Function.update t.ptrs (3 * d + b) v, t.mem⟩
      ⟨p2, s.regs, Function.update s.ptrs d v, s.mem⟩ := by
  refine ⟨h.regs, fun i => ?_, h.mem, h.fregs, fun i hi hi2 => ?_, h.fmem⟩
  · by_cases hid : i = d
    · subst hid; simp
    · have : 3 * i + b ≠ 3 * d + b := by omega
      simp [Function.update_of_ne this, Function.update_of_ne hid, h.ptrs]
  · have : i ≠ 3 * d + b := by omega
    simp [Function.update_of_ne this, h.fptrs i hi hi2]

lemma CRel_mem {b c sp : ℕ} {c0 t s : RAMConfig} (h : CRel b c sp c0 t s) (hc : c < 2) (p1 p2 : ℕ) (z : ℤ)
    (v : ℝ) :
    CRel b c sp c0 ⟨p1, t.regs, t.ptrs, Function.update t.mem (2 * z + c) v⟩
      ⟨p2, s.regs, s.ptrs, Function.update s.mem z v⟩ := by
  refine ⟨h.regs, h.ptrs, fun y => ?_, h.fregs, h.fptrs, fun y hy => ?_⟩
  · by_cases hyz : y = z
    · subst hyz; simp
    · have : 2 * y + (c : ℤ) ≠ 2 * z + c := by omega
      simp [Function.update_of_ne this, Function.update_of_ne hyz, h.mem]
  · have : y ≠ 2 * z + c := by omega
    simp [Function.update_of_ne this, h.fmem y hy]

lemma CRel_sp {b c sp : ℕ} {c0 t s : RAMConfig} (h : CRel b c sp c0 t s) (hb : b < 3) (hsp : sp % 3 ≠ b)
    (p1 : ℕ) (v : ℤ) :
    CRel b c sp c0 ⟨p1, t.regs, Function.update t.ptrs sp v, t.mem⟩ s := by
  refine ⟨h.regs, fun i => ?_, h.mem, h.fregs, fun i hi hi2 => ?_, h.fmem⟩
  · have : 3 * i + b ≠ sp := by omega
    simp [Function.update_of_ne this, h.ptrs]
  · simp [Function.update_of_ne hi2, h.fptrs i hi hi2]

lemma step_nop (P : Program) (s : State) (sp : ℕ) (hh : s.halted = false)
    (h : P[s.core.pc]? = some (nop sp)) :
    step P s = ⟨⟨s.core.pc + 1, s.core.regs, s.core.ptrs, s.core.mem⟩, false, s.work + 1,
      s.inputLength⟩ := by
  rw [step_core P s _ hh h]; simp [coreExec]

lemma nopnop (P : Program) (s : State) (sp : ℕ) (hh : s.halted = false)
    (h0 : P[s.core.pc]? = some (nop sp)) (h1 : P[s.core.pc + 1]? = some (nop sp)) :
    (step P)^[2] s = ⟨⟨s.core.pc + 2, s.core.regs, s.core.ptrs, s.core.mem⟩, false, s.work + 2,
      s.inputLength⟩ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [step_nop P s sp hh h0, step_nop P _ sp rfl h1]


lemma three_core (P : Program) (t : State) (sp q : ℕ) (X : RAMInstr) (hh : t.halted = false)
    (hpc : t.core.pc = q) (h0 : P[q]? = some (nop sp)) (h1 : P[q + 1]? = some (nop sp))
    (h2 : P[q + 2]? = some (.core X)) :
    (step P)^[3] t = ⟨coreExec X ⟨q + 2, t.core.regs, t.core.ptrs, t.core.mem⟩, false,
      t.work + 3, t.inputLength⟩ := by
  rw [show (step P)^[3] t = step P ((step P)^[2] t) from Function.iterate_succ_apply' _ _ _,
    nopnop P t sp hh (hpc ▸ h0) (hpc ▸ h1)]
  rw [step_core P _ X rfl (by simpa [hpc] using h2)]
  simp [hpc]

lemma three_eq (P : Program) (t : State) : (step P)^[3] t = step P (step P (step P t)) := rfl

lemma time_step3 (t0 t s : State) (h : TimeOK t0 t s) (w1 L1 w2 L2 : ℕ)
    (h1 : w1 = t.work + 3) (h2 : L1 = t.inputLength) (h3 : w2 = s.work + 1)
    (h4 : L2 = s.inputLength) :
    w1 + L1 ≤ t0.work + t0.inputLength + 3 * (w2 + L2) := by
  unfold TimeOK at h; omega

lemma floor_wait (P : Program) (d a K : ℕ) : ∀ (n : ℕ) (t : State), t.halted = false →
    P[t.core.pc]? = some (.floorPtr d a K) →
    |⌊t.core.regs a⌋| ≤ (K : ℤ) * (((t.work + n : ℕ) : ℤ) + (t.inputLength : ℤ) + 1) →
    ∃ j ≤ n, (step P)^[j] t = ⟨t.core, false, t.work + j, t.inputLength⟩ ∧
      |⌊t.core.regs a⌋| ≤ (K : ℤ) * (((t.work + j : ℕ) : ℤ) + (t.inputLength : ℤ) + 1)
  | 0, t, hh, _, hg => ⟨0, le_rfl, by rw [← hh]; rfl, hg⟩
  | n + 1, t, hh, hp, hg => by
    by_cases h0 : |⌊t.core.regs a⌋| ≤ (K : ℤ) * ((t.work : ℤ) + (t.inputLength : ℤ) + 1)
    · exact ⟨0, by omega, by rw [← hh]; rfl, by simpa using h0⟩
    · have hs := step_floor_fail P t d a K hh hp h0
      obtain ⟨j, hj, he, hg'⟩ := floor_wait P d a K n { t with work := t.work + 1 } hh hp
        (by simpa [add_assoc, add_comm 1 n] using hg)
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, hs, he]; simp [add_assoc, add_comm 1 j]
      · simpa [add_assoc, add_comm 1 j] using hg'

lemma sim_step (Q R : Program) (b c base cont sp : ℕ) (hb : b < 3) (hsp : sp % 3 ≠ b)
    (hc : c = 0 ∨ c = 1) (hE : Embeds R Q b c base cont sp) (t0 t s : State)
    (hG : Good b c sp t0 t s) (hpc : t.core.pc = base + 3 * s.core.pc) (hs : s.halted = false)
    (hT : TimeOK t0 t s) (hnh : Q[s.core.pc]? ≠ some .halt) :
    ∃ j, Good b c sp t0 ((step R)^[j] t) (step Q s) ∧
      ((step R)^[j] t).core.pc = base + 3 * (step Q s).core.pc ∧
      (step Q s).halted = false ∧ TimeOK t0 ((step R)^[j] t) (step Q s) := by
  obtain ⟨hth, hlen, hR⟩ := hG
  cases hq : Q[s.core.pc]? with
  | none =>
    refine ⟨0, ?_⟩
    rw [step_none Q s hs hq]
    refine ⟨⟨hth, hlen, hR⟩, hpc, hs, ?_⟩
    unfold TimeOK at hT ⊢; simp; omega
  | some ins =>
    obtain ⟨e0, e1, e2⟩ := hE _ _ hq
    cases ins with
    | core i =>
      cases i with
      | const d v =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec]
        exact ⟨⟨rfl, hlen, CRel_regs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | add d i j =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.regs]
        exact ⟨⟨rfl, hlen, CRel_regs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | sub d i j =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.regs]
        exact ⟨⟨rfl, hlen, CRel_regs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | mul d i j =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.regs]
        exact ⟨⟨rfl, hlen, CRel_regs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | div d i j =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.regs]
        exact ⟨⟨rfl, hlen, CRel_regs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | pset q v =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec]
        exact ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | pcopy q q' =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.ptrs]
        exact ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | pinc q =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.ptrs]
        exact ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | pdec q =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.ptrs]
        exact ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by omega, by simp,
          time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | jle i T =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.regs]
        split_ifs
        · exact ⟨⟨rfl, hlen, CRel_pc hR _ _⟩, rfl, by simp,
            time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
        · exact ⟨⟨rfl, hlen, CRel_pc hR _ _⟩, by dsimp only; omega, by simp,
            time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | pjle q q' T =>
        refine ⟨3, ?_⟩
        rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_core Q s _ hs hq]
        simp only [coreExec, hR.ptrs]
        split_ifs
        · exact ⟨⟨rfl, hlen, CRel_pc hR _ _⟩, rfl, by simp,
            time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
        · exact ⟨⟨rfl, hlen, CRel_pc hR _ _⟩, by dsimp only; omega, by simp,
            time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | accept =>
        refine ⟨0, ?_⟩
        rw [step_core Q s _ hs hq]
        simp only [coreExec]
        refine ⟨⟨hth, hlen, hR⟩, hpc, by simp, ?_⟩
        unfold TimeOK at hT ⊢; simp; omega
      | reject =>
        refine ⟨0, ?_⟩
        rw [step_core Q s _ hs hq]
        simp only [coreExec]
        refine ⟨⟨hth, hlen, hR⟩, hpc, by simp, ?_⟩
        unfold TimeOK at hT ⊢; simp; omega
      | load d q =>
        refine ⟨3, ?_⟩
        rw [← hpc] at e0 e1 e2
        simp only [tr] at e0 e1 e2
        rw [three_eq, step_padd R t _ _ _ hth e0]
        rcases hc with rfl | rfl
        · simp only [show ((0 : ℕ) = 1) = False from by simp, if_false] at e1
          rw [step_nop R (⟨⟨t.core.pc + 1, _, _, _⟩, false, _, _⟩ : State) sp rfl e1, step_core R _ _ rfl e2, step_core Q s _ hs hq]
          simp only [coreExec, Function.update_self, hR.ptrs]
          have hm := hR.mem (s.core.ptrs q)
          simp only [Nat.cast_zero, add_zero] at hm
          rw [show s.core.ptrs q + s.core.ptrs q = 2 * s.core.ptrs q by ring, hm]
          exact ⟨⟨rfl, hlen, CRel_regs (CRel_sp hR hb hsp 0 _) hb _ _ _ _⟩, by omega, by simp,
            time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
        · simp only [if_true] at e1
          rw [step_core R (⟨⟨t.core.pc + 1, _, _, _⟩, false, _, _⟩ : State) _ rfl e1, step_core R _ _ rfl e2, step_core Q s _ hs hq]
          simp only [coreExec, Function.update_self, hR.ptrs]
          have hm := hR.mem (s.core.ptrs q)
          simp only [Nat.cast_one] at hm
          rw [show s.core.ptrs q + s.core.ptrs q + 1 = 2 * s.core.ptrs q + 1 by ring, hm]
          exact ⟨⟨rfl, hlen, CRel_regs (CRel_sp (CRel_sp hR hb hsp 0 _) hb hsp 0 _) hb _ _ _ _⟩,
            by omega, by simp, time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
      | store q i =>
        refine ⟨3, ?_⟩
        rw [← hpc] at e0 e1 e2
        simp only [tr] at e0 e1 e2
        rw [three_eq, step_padd R t _ _ _ hth e0]
        rcases hc with rfl | rfl
        · simp only [show ((0 : ℕ) = 1) = False from by simp, if_false] at e1
          rw [step_nop R (⟨⟨t.core.pc + 1, _, _, _⟩, false, _, _⟩ : State) sp rfl e1, step_core R _ _ rfl e2, step_core Q s _ hs hq]
          simp only [coreExec, Function.update_self, hR.ptrs]
          have hr : t.core.regs (3 * i + b) = s.core.regs i := hR.regs i
          rw [hr,
            show s.core.ptrs q + s.core.ptrs q = 2 * s.core.ptrs q + ((0 : ℕ) : ℤ) by push_cast; ring]
          exact ⟨⟨rfl, hlen, CRel_mem (CRel_sp hR hb hsp 0 _) (by omega) _ _ _ _⟩,
            by omega, by simp, time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
        · simp only [if_true] at e1
          rw [step_core R (⟨⟨t.core.pc + 1, _, _, _⟩, false, _, _⟩ : State) _ rfl e1, step_core R _ _ rfl e2, step_core Q s _ hs hq]
          simp only [coreExec, Function.update_self, hR.ptrs]
          have hr : t.core.regs (3 * i + b) = s.core.regs i := hR.regs i
          rw [hr,
            show s.core.ptrs q + s.core.ptrs q + 1 = 2 * s.core.ptrs q + ((1 : ℕ) : ℤ) by
              push_cast; ring]
          exact ⟨⟨rfl, hlen, CRel_mem (CRel_sp (CRel_sp hR hb hsp 0 _) hb hsp 0 _) (by omega) _ _ _ _⟩,
            by omega, by simp, time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
    | padd d x y =>
      refine ⟨3, ?_⟩
      rw [← hpc] at e0 e1 e2
      simp only [tr] at e0 e1 e2
      rw [show (step R)^[3] t = step R ((step R)^[2] t) from Function.iterate_succ_apply' _ _ _,
        nopnop R t sp hth e0 e1, step_padd R _ _ _ _ rfl e2, step_padd Q s _ _ _ hs hq]
      simp only [hR.ptrs]
      exact ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by omega, by simp,
        time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
    | psub d x y =>
      refine ⟨3, ?_⟩
      rw [← hpc] at e0 e1 e2
      simp only [tr] at e0 e1 e2
      rw [show (step R)^[3] t = step R ((step R)^[2] t) from Function.iterate_succ_apply' _ _ _,
        nopnop R t sp hth e0 e1, step_psub R _ _ _ _ rfl e2, step_psub Q s _ _ _ hs hq]
      simp only [hR.ptrs]
      exact ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by omega, by simp,
        time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
    | ofPtr d x =>
      refine ⟨3, ?_⟩
      rw [← hpc] at e0 e1 e2
      simp only [tr] at e0 e1 e2
      rw [show (step R)^[3] t = step R ((step R)^[2] t) from Function.iterate_succ_apply' _ _ _,
        nopnop R t sp hth e0 e1, step_ofPtr R _ _ _ rfl e2, step_ofPtr Q s _ _ hs hq]
      simp only [hR.ptrs]
      exact ⟨⟨rfl, hlen, CRel_regs hR hb _ _ _ _⟩, by omega, by simp,
        time_step3 t0 t s hT _ _ _ _ rfl rfl rfl rfl⟩
    | floorPtr d x K =>
      rw [← hpc] at e0 e1 e2
      simp only [tr] at e0 e1 e2
      have hxr : t.core.regs (3 * x + b) = s.core.regs x := hR.regs x
      by_cases hgs : |⌊s.core.regs x⌋| ≤ (K : ℤ) * ((s.work : ℤ) + (s.inputLength : ℤ) + 1)
      · obtain ⟨j, hj, he, hg'⟩ := floor_wait R (3 * d + b) (3 * x + b) K
          ((s.work + s.inputLength) - (t.work + t.inputLength)) t hth e0 (by
            rw [hxr]
            refine hgs.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
            push_cast
            have : ((s.work + s.inputLength : ℕ) : ℤ) ≤
              ((t.work + ((s.work + s.inputLength) - (t.work + t.inputLength)) + t.inputLength : ℕ) : ℤ) := by
              exact_mod_cast (by omega)
            push_cast at this; linarith)
        refine ⟨3 + j, ?_⟩
        rw [Function.iterate_add_apply, he, three_eq,
          step_floor_pass R (⟨t.core, false, t.work + j, t.inputLength⟩ : State) _ _ _ rfl e0 hg',
          step_nop R (⟨⟨t.core.pc + 1, _, _, _⟩, false, _, _⟩ : State) sp rfl e1,
          step_nop R (⟨⟨t.core.pc + 1 + 1, _, _, _⟩, false, _, _⟩ : State) sp rfl e2,
          step_floor_pass Q s _ _ _ hs hq hgs]
        rw [hxr]
        refine ⟨⟨rfl, hlen, CRel_ptrs hR hb _ _ _ _⟩, by dsimp only; omega, by simp, ?_⟩
        unfold TimeOK at hT ⊢; dsimp only; omega
      · refine ⟨0, ?_⟩
        rw [step_floor_fail Q s _ _ _ hs hq hgs]
        refine ⟨⟨hth, hlen, hR⟩, by rw [← hpc]; rfl, by simp [hs], ?_⟩
        unfold TimeOK at hT ⊢; simp; omega
    | halt => exact absurd hq hnh


lemma iterate_halted (P : Program) (s : State) (h : s.halted = true) (k : ℕ) :
    (step P)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, step_halted P s h]

lemma step_work_len (P : Program) (s : State) (hh : s.halted = false) :
    (step P s).work = s.work + 1 ∧ (step P s).inputLength = s.inputLength := by
  unfold step
  simp only [hh, Bool.false_eq_true, if_false]
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

lemma step_len (P : Program) (s : State) : (step P s).inputLength = s.inputLength := by
  cases hh : s.halted
  · exact (step_work_len P s hh).2
  · rw [step_halted P s hh]

lemma sim_halt (Q R : Program) (b c base cont sp : ℕ) (hE : Embeds R Q b c base cont sp)
    (t0 t s : State) (hG : Good b c sp t0 t s) (hpc : t.core.pc = base + 3 * s.core.pc)
    (hs : s.halted = false) (hT : TimeOK t0 t s) (hq : Q[s.core.pc]? = some .halt) :
    Good b c sp t0 ((step R)^[3] t) (step Q s) ∧ ((step R)^[3] t).core.pc = cont ∧
      ((step R)^[3] t).work + ((step R)^[3] t).inputLength ≤
        t0.work + t0.inputLength + 3 * (s.work + s.inputLength) + 3 := by
  obtain ⟨hth, hlen, hR⟩ := hG
  obtain ⟨e0, e1, e2⟩ := hE _ _ hq
  rw [three_core R t sp _ _ hth hpc e0 e1 e2, step_halt Q s hs hq]
  simp only [coreExec, le_refl, if_true]
  refine ⟨⟨by simp, hlen, CRel_pc hR _ _⟩, by simp, ?_⟩
  unfold TimeOK at hT; omega

lemma sim_run (Q R : Program) (b c base cont sp : ℕ) (hb : b < 3) (hsp : sp % 3 ≠ b)
    (hc : c = 0 ∨ c = 1) (hE : Embeds R Q b c base cont sp) (t0 : State) (k : ℕ) :
    ∀ (s t : State), Good b c sp t0 t s → t.core.pc = base + 3 * s.core.pc →
      s.halted = false → TimeOK t0 t s → ((step Q)^[k] s).halted = true →
      ∃ j, Good b c sp t0 ((step R)^[j] t) ((step Q)^[k] s) ∧
        ((step R)^[j] t).core.pc = cont ∧
        ((step R)^[j] t).work + ((step R)^[j] t).inputLength ≤
          t0.work + t0.inputLength + 3 * (s.work + k + s.inputLength) + 3 := by
  induction k with
  | zero => intro s t _ _ hs _ hk; simp [hs] at hk
  | succ k ih =>
    intro s t hG hpc hs hT hk
    rw [Function.iterate_succ_apply] at hk ⊢
    by_cases hq : Q[s.core.pc]? = some .halt
    · have hh : (step Q s).halted = true := by rw [step_halt Q s hs hq]
      rw [iterate_halted Q _ hh]
      obtain ⟨h1, h2, h3⟩ := sim_halt Q R b c base cont sp hE t0 t s hG hpc hs hT hq
      exact ⟨3, h1, h2, by omega⟩
    · obtain ⟨j1, h1, h2, h3, h4⟩ :=
        sim_step Q R b c base cont sp hb hsp hc hE t0 t s hG hpc hs hT hq
      obtain ⟨j2, g1, g2, g3⟩ := ih _ _ h1 h2 h3 h4 hk
      refine ⟨j2 + j1, ?_⟩
      rw [Function.iterate_add_apply]
      obtain ⟨hw, hl⟩ := step_work_len Q s hs
      rw [hw, hl] at g3
      exact ⟨g1, g2, by omega⟩

lemma output_of_halted (P : Program) (xs : List ℝ) (k : ℕ) (h : (run P xs k).halted = true) :
    output P xs = some (outputOf (run P xs k)) := by
  have hex : ∃ k, (run P xs k).halted = true := ⟨k, h⟩
  unfold output
  rw [dif_pos hex]
  have hle : Nat.find hex ≤ k := Nat.find_min' hex h
  have hk : run P xs k = run P xs (Nat.find hex) := by
    unfold run
    rw [show k = (k - Nat.find hex) + Nat.find hex by omega, Function.iterate_add_apply]
    exact iterate_halted P _ (Nat.find_spec hex) _
  rw [hk]

lemma halted_of_output (P : Program) (xs : List ℝ) (l : List ℝ) (h : output P xs = some l) :
    ∃ k, (run P xs k).halted = true ∧ outputOf (run P xs k) = l ∧
      ∀ k', (run P xs k').halted = true → k ≤ k' := by
  unfold output at h
  split_ifs at h with hex
  exact ⟨Nat.find hex, Nat.find_spec hex, Option.some_inj.mp h, fun k' hk' => Nat.find_min' hex hk'⟩

/-! explicit-state step lemmas -/
lemma xs_core (R : Program) (pc w L : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (i : RAMInstr)
    (h : R[pc]? = some (.core i)) :
    step R ⟨⟨pc, r, p, m⟩, false, w, L⟩ = ⟨coreExec i ⟨pc, r, p, m⟩, false, w + 1, L⟩ :=
  step_core R _ i rfl h

lemma xs_padd (R : Program) (pc w L : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (d a b : ℕ)
    (h : R[pc]? = some (.padd d a b)) :
    step R ⟨⟨pc, r, p, m⟩, false, w, L⟩ =
      ⟨⟨pc + 1, r, Function.update p d (p a + p b), m⟩, false, w + 1, L⟩ := by
  simp [step, h]

lemma xs_psub (R : Program) (pc w L : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (d a b : ℕ)
    (h : R[pc]? = some (.psub d a b)) :
    step R ⟨⟨pc, r, p, m⟩, false, w, L⟩ =
      ⟨⟨pc + 1, r, Function.update p d (p a - p b), m⟩, false, w + 1, L⟩ := by
  simp [step, h]

lemma xs_ofPtr (R : Program) (pc w L : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (d a : ℕ)
    (h : R[pc]? = some (.ofPtr d a)) :
    step R ⟨⟨pc, r, p, m⟩, false, w, L⟩ =
      ⟨⟨pc + 1, Function.update r d (p a : ℝ), p, m⟩, false, w + 1, L⟩ := by
  simp [step, h]

lemma xs_floor (R : Program) (pc w L : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (d a K : ℕ)
    (h : R[pc]? = some (.floorPtr d a K))
    (hg : |⌊r a⌋| ≤ (K : ℤ) * ((w : ℤ) + (L : ℤ) + 1)) :
    step R ⟨⟨pc, r, p, m⟩, false, w, L⟩ =
      ⟨⟨pc + 1, r, Function.update p d ⌊r a⌋, m⟩, false, w + 1, L⟩ := by
  simp [step, h, hg]

lemma xs_halt (R : Program) (pc w L : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (h : R[pc]? = some .halt) :
    step R ⟨⟨pc, r, p, m⟩, false, w, L⟩ = ⟨⟨pc + 1, r, p, m⟩, true, w + 1, L⟩ := by
  simp [step, h]

def segA : List Instr :=
  [.core (.pset 9 (-1)), .core (.pset 0 0), .core (.load 0 0), .floorPtr 3 0 1,
   .core (.pjle 3 9 12), .core (.load 0 3), .padd 6 3 3, .core (.store 6 3), .core (.pinc 6),
   .core (.store 6 0), .core (.pdec 3), .core (.pjle 9 9 4)]

/-- memory during segment A after processing cells `> i`. -/
noncomputable def memA (L : ℕ) (M0 : ℤ → ℝ) (i : ℤ) (y : ℤ) : ℝ :=
  if 2 * i + 2 ≤ y ∧ y ≤ 2 * (L : ℤ) + 1 then (if y % 2 = 0 then 0 else M0 ((y - 1) / 2))
  else M0 y

lemma segA_body (R : Program) (hA : ∀ k < 12, R[k]? = segA[k]?) (r : ℕ → ℝ) (p : ℕ → ℤ)
    (M : ℤ → ℝ) (w L' : ℕ) (hlt : ¬ p 3 ≤ p 9) :
    (step R)^[8] ⟨⟨4, r, p, M⟩, false, w, L'⟩ =
      ⟨⟨4, Function.update r 0 (M (p 3)),
        Function.update (Function.update (Function.update p 6 (p 3 + p 3)) 6 (p 3 + p 3 + 1)) 3
          (p 3 - 1),
        Function.update (Function.update M (p 3 + p 3) (r 3)) (p 3 + p 3 + 1) (M (p 3))⟩,
        false, w + 8, L'⟩ := by
  have h4 : R[4]? = some (.core (.pjle 3 9 12)) := by rw [hA 4 (by norm_num)]; rfl
  have h5 : R[5]? = some (.core (.load 0 3)) := by rw [hA 5 (by norm_num)]; rfl
  have h6 : R[6]? = some (.padd 6 3 3) := by rw [hA 6 (by norm_num)]; rfl
  have h7 : R[7]? = some (.core (.store 6 3)) := by rw [hA 7 (by norm_num)]; rfl
  have h8 : R[8]? = some (.core (.pinc 6)) := by rw [hA 8 (by norm_num)]; rfl
  have h9 : R[9]? = some (.core (.store 6 0)) := by rw [hA 9 (by norm_num)]; rfl
  have h10 : R[10]? = some (.core (.pdec 3)) := by rw [hA 10 (by norm_num)]; rfl
  have h11 : R[11]? = some (.core (.pjle 9 9 4)) := by rw [hA 11 (by norm_num)]; rfl
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [xs_core R _ _ _ _ _ _ _ h4]
  simp only [coreExec, if_neg hlt, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ h5]
  simp only [coreExec, Nat.reduceAdd]
  rw [xs_padd R _ _ _ _ _ _ _ _ _ h6]
  simp only [Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ h7]
  simp only [coreExec, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ h8]
  simp only [coreExec, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ h9]
  simp only [coreExec, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ h10]
  simp only [coreExec, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ h11]
  simp only [coreExec, Nat.reduceAdd, le_refl, if_true]
  simp

lemma segA_loop (R : Program) (hA : ∀ k < 12, R[k]? = segA[k]?) (L : ℕ) (M0 : ℤ → ℝ) :
    ∀ (n : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w L' : ℕ), n ≤ L + 1 →
      p 9 = -1 → p 3 = (n : ℤ) - 1 → r 3 = 0 →
      ∃ r' p' m', (step R)^[8 * n + 1] ⟨⟨4, r, p, memA L M0 ((n : ℤ) - 1)⟩, false, w, L'⟩ =
        ⟨⟨12, r', p', m'⟩, false, w + 8 * n + 1, L'⟩ ∧
        (∀ k, k % 3 ≠ 0 → r' k = r k) ∧ (∀ k, k % 3 ≠ 0 → p' k = p k) ∧
        m' = memA L M0 (-1) := by
  have h4 : R[4]? = some (.core (.pjle 3 9 12)) := by rw [hA 4 (by norm_num)]; rfl
  have h5 : R[5]? = some (.core (.load 0 3)) := by rw [hA 5 (by norm_num)]; rfl
  have h6 : R[6]? = some (.padd 6 3 3) := by rw [hA 6 (by norm_num)]; rfl
  have h7 : R[7]? = some (.core (.store 6 3)) := by rw [hA 7 (by norm_num)]; rfl
  have h8 : R[8]? = some (.core (.pinc 6)) := by rw [hA 8 (by norm_num)]; rfl
  have h9 : R[9]? = some (.core (.store 6 0)) := by rw [hA 9 (by norm_num)]; rfl
  have h10 : R[10]? = some (.core (.pdec 3)) := by rw [hA 10 (by norm_num)]; rfl
  have h11 : R[11]? = some (.core (.pjle 9 9 4)) := by rw [hA 11 (by norm_num)]; rfl
  intro n
  induction n with
  | zero =>
    intro r p w L' _ h9' h3 _
    refine ⟨r, p, memA L M0 (-1), ?_, fun _ _ => rfl, fun _ _ => rfl, rfl⟩
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_one]
    rw [xs_core R _ _ _ _ _ _ _ h4]
    simp [coreExec, h9', h3]
  | succ n ih =>
    intro r p w L' hn h9' h3 hr3
    rw [show 8 * (n + 1) + 1 = (8 * n + 1) + 8 by ring, Function.iterate_add_apply,
      segA_body R hA _ _ _ _ _ (by rw [h9', h3]; push_cast; omega)]
    have hM : Function.update (Function.update (memA L M0 ((((n + 1 : ℕ) : ℤ)) - 1))
        (p 3 + p 3) (r 3)) (p 3 + p 3 + 1) (memA L M0 ((((n + 1 : ℕ) : ℤ)) - 1) (p 3)) =
        memA L M0 ((n : ℤ) - 1) := by
      funext y
      rw [h3, hr3]
      push_cast
      simp only [Function.update_apply, memA]
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
    rw [hM]
    obtain ⟨r', p', m', he, hr', hp', hm'⟩ := ih (Function.update r 0 _)
      (Function.update (Function.update (Function.update p 6 (p 3 + p 3)) 6 (p 3 + p 3 + 1)) 3
          (p 3 - 1)) (w + 8) L' (by omega) (by simp [h9']) (by simp [h3])
      (by simp [hr3])
    refine ⟨r', p', m', ?_, fun k hk => ?_, fun k hk => ?_, hm'⟩
    · rw [he, show w + 8 + 8 * n + 1 = w + 8 * (n + 1) + 1 by ring]
    · rw [hr' k hk]
      have : k ≠ 0 := by omega
      simp [this]
    · rw [hp' k hk]
      have : k ≠ 3 := by omega
      have : k ≠ 6 := by omega
      simp [*]


lemma initMem_out (xs : List ℝ) (z : ℤ) (h : z < 0 ∨ (xs.length : ℤ) < z) :
    (initState xs).core.mem z = 0 := by
  simp only [initState]
  rcases h with h | h
  · rw [if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_pos (by omega)]
    apply List.getD_eq_default
    omega

lemma segA_spec (R : Program) (hA : ∀ k < 12, R[k]? = segA[k]?) (xs : List ℝ) :
    ∃ r p m, (step R)^[8 * xs.length + 13] (initState xs) =
      ⟨⟨12, r, p, m⟩, false, 8 * xs.length + 13, xs.length⟩ ∧
      (∀ k, k % 3 ≠ 0 → r k = 0) ∧ (∀ k, k % 3 ≠ 0 → p k = 0) ∧
      (∀ z, m (2 * z + 1) = (initState xs).core.mem z) ∧ (∀ z, m (2 * z) = 0) := by
  have h0 : R[0]? = some (.core (.pset 9 (-1))) := by rw [hA 0 (by norm_num)]; rfl
  have h1 : R[1]? = some (.core (.pset 0 0)) := by rw [hA 1 (by norm_num)]; rfl
  have h2 : R[2]? = some (.core (.load 0 0)) := by rw [hA 2 (by norm_num)]; rfl
  have h3 : R[3]? = some (.floorPtr 3 0 1) := by rw [hA 3 (by norm_num)]; rfl
  set M0 := (initState xs).core.mem with hM0
  set L := xs.length with hL
  have hinit : initState xs = ⟨⟨0, fun _ => 0, fun _ => 0, M0⟩, false, 0, L⟩ := rfl
  have hM00 : M0 0 = (L : ℝ) := by simp [hM0, initState, hL]
  have hpre : (step R)^[4] (initState xs) = ⟨⟨4, Function.update (fun _ => 0) 0 (L : ℝ),
      Function.update (Function.update (Function.update (fun _ => 0) 9 (-1)) 0 0) 3 (L : ℤ),
      M0⟩, false, 4, L⟩ := by
    rw [hinit, show (step R)^[4] (⟨⟨0, fun _ => 0, fun _ => 0, M0⟩, false, 0, L⟩ : State) =
      step R (step R (step R (step R ⟨⟨0, fun _ => 0, fun _ => 0, M0⟩, false, 0, L⟩))) from rfl]
    rw [xs_core R _ _ _ _ _ _ _ h0]
    simp only [coreExec, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ h1]
    simp only [coreExec, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ h2]
    simp only [coreExec, Nat.reduceAdd, Function.update_self, hM00]
    rw [xs_floor R _ _ _ _ _ _ _ _ _ h3 (by simp; omega)]
    simp only [Nat.reduceAdd, Function.update_self, Int.floor_natCast]
  have hM : M0 = memA L M0 (((L + 1 : ℕ) : ℤ) - 1) := by
    funext y; simp only [memA]; rw [if_neg (by push_cast; omega)]
  rw [show 8 * L + 13 = (8 * (L + 1) + 1) + 4 by ring, Function.iterate_add_apply, hpre]
  obtain ⟨r', p', m', he, hr', hp', hm'⟩ := segA_loop R hA L M0 (L + 1)
    (Function.update (fun _ => 0) 0 (L : ℝ))
    (Function.update (Function.update (Function.update (fun _ => 0) 9 (-1)) 0 0) 3 (L : ℤ))
    4 L le_rfl (by simp) (by simp) (by simp)
  rw [← hM] at he
  refine ⟨r', p', m', ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [he]; ring_nf
  · rw [hr' k hk]
    have : k ≠ 0 := by omega
    simp [this]
  · rw [hp' k hk]
    have : k ≠ 3 := by omega
    have : k ≠ 9 := by omega
    have : k ≠ 0 := by omega
    simp [*]
  · intro z
    rw [hm']; simp only [memA]
    split_ifs with h1 h2
    · omega
    · congr 1; omega
    · simp only [hM0, initMem_out xs z (by omega), initMem_out xs (2 * z + 1) (by omega)]
  · intro z
    rw [hm']; simp only [memA]
    split_ifs with h1 h2
    · rfl
    · omega
    · rw [hM0]; exact initMem_out xs (2 * z) (by omega)


def segD (o : ℕ) : List Instr :=
  [.core (.pset 0 (-1)), .core (.load 0 0), .core (.jle 0 (o + 33)),
   .core (.pset 3 (-3)), .core (.load 3 3), .core (.pset 3 (-5)), .core (.load 6 3),
   .core (.add 9 3 3), .core (.div 9 6 9), .core (.const 15 1), .core (.sub 18 9 15),
   .core (.jle 18 (o + 13)), .core (.const 9 1),
   .ofPtr 18 1, .core (.const 21 2), .core (.sub 18 18 21),
   .core (.pset 0 0), .core (.store 0 18), .core (.pset 0 2), .core (.store 0 9),
   .core (.pset 3 4), .core (.pset 6 (-7)), .core (.pset 15 2), .padd 9 1 1, .psub 9 9 15,
   .core (.pjle 9 3 (o + 37)),
   .core (.load 24 6), .core (.store 3 24), .core (.pinc 3), .core (.pinc 3),
   .core (.pdec 6), .core (.pdec 6), .core (.pjle 0 0 (o + 25)),
   .core (.const 0 0), .core (.store 0 0), .core (.pset 0 1), .halt]

lemma segD_no (R : Program) (o : ℕ) (hD : ∀ k < 37, R[o + k]? = (segD o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (w L : ℕ) (h0 : m (-1) ≤ 0) :
    ((step R)^[7] ⟨⟨o, r, p, m⟩, false, w, L⟩).halted = true ∧
      outputOf ((step R)^[7] ⟨⟨o, r, p, m⟩, false, w, L⟩) = [0] := by
  have e0 : R[o]? = some (.core (.pset 0 (-1))) := by rw [← Nat.add_zero o, hD 0 (by norm_num)]; rfl
  have e1 : R[o + 1]? = some (.core (.load 0 0)) := by rw [hD 1 (by norm_num)]; rfl
  have e2 : R[o + 2]? = some (.core (.jle 0 (o + 33))) := by rw [hD 2 (by norm_num)]; rfl
  have e33 : R[o + 33]? = some (.core (.const 0 0)) := by rw [hD 33 (by norm_num)]; rfl
  have e34 : R[o + 34]? = some (.core (.store 0 0)) := by rw [hD 34 (by norm_num)]; rfl
  have e35 : R[o + 35]? = some (.core (.pset 0 1)) := by rw [hD 35 (by norm_num)]; rfl
  have e36 : R[o + 36]? = some .halt := by rw [hD 36 (by norm_num)]; rfl
  have hx : (step R)^[7] (⟨⟨o, r, p, m⟩, false, w, L⟩ : State) = step R (step R (step R
      (step R (step R (step R (step R ⟨⟨o, r, p, m⟩, false, w, L⟩)))))) := rfl
  rw [hx]
  rw [xs_core R _ _ _ _ _ _ _ e0]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e1]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self]
  rw [xs_core R _ _ _ _ _ _ _ e2]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self, h0, if_true]
  rw [xs_core R _ _ _ _ _ _ _ e33]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e34]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e35]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_halt R _ _ _ _ _ _ e36]
  refine ⟨rfl, ?_⟩
  simp [outputOf]


lemma segD_pre1 (R : Program) (o : ℕ) (hD : ∀ k < 37, R[o + k]? = (segD o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (w L : ℕ) (h0 : ¬ m (-1) ≤ 0) :
    ∃ k r1 p1, k ≤ 13 ∧ (step R)^[k] ⟨⟨o, r, p, m⟩, false, w, L⟩ =
      ⟨⟨o + 13, r1, p1, m⟩, false, w + k, L⟩ ∧
      r1 9 = (if m (-5) / (m (-3) + m (-3)) - 1 ≤ 0 then m (-5) / (m (-3) + m (-3)) else 1) ∧
      (∀ k, k % 3 ≠ 0 → r1 k = r k) ∧ (∀ k, k % 3 ≠ 0 → p1 k = p k) := by
  have e0 : R[o]? = some (.core (.pset 0 (-1))) := by rw [← Nat.add_zero o, hD 0 (by norm_num)]; rfl
  have e1 : R[o + 1]? = some (.core (.load 0 0)) := by rw [hD 1 (by norm_num)]; rfl
  have e2 : R[o + 2]? = some (.core (.jle 0 (o + 33))) := by rw [hD 2 (by norm_num)]; rfl
  have e3 : R[o + 3]? = some (.core (.pset 3 (-3))) := by rw [hD 3 (by norm_num)]; rfl
  have e4 : R[o + 4]? = some (.core (.load 3 3)) := by rw [hD 4 (by norm_num)]; rfl
  have e5 : R[o + 5]? = some (.core (.pset 3 (-5))) := by rw [hD 5 (by norm_num)]; rfl
  have e6 : R[o + 6]? = some (.core (.load 6 3)) := by rw [hD 6 (by norm_num)]; rfl
  have e7 : R[o + 7]? = some (.core (.add 9 3 3)) := by rw [hD 7 (by norm_num)]; rfl
  have e8 : R[o + 8]? = some (.core (.div 9 6 9)) := by rw [hD 8 (by norm_num)]; rfl
  have e9 : R[o + 9]? = some (.core (.const 15 1)) := by rw [hD 9 (by norm_num)]; rfl
  have e10 : R[o + 10]? = some (.core (.sub 18 9 15)) := by rw [hD 10 (by norm_num)]; rfl
  have e11 : R[o + 11]? = some (.core (.jle 18 (o + 13))) := by rw [hD 11 (by norm_num)]; rfl
  have e12 : R[o + 12]? = some (.core (.const 9 1)) := by rw [hD 12 (by norm_num)]; rfl
  have hx : (step R)^[11] (⟨⟨o, r, p, m⟩, false, w, L⟩ : State) = step R (step R (step R
      (step R (step R (step R (step R (step R (step R (step R (step R
        ⟨⟨o, r, p, m⟩, false, w, L⟩)))))))))) := rfl
  have h11 : ∃ r1 : ℕ → ℝ, ∃ p1 : ℕ → ℤ, (step R)^[11] (⟨⟨o, r, p, m⟩, false, w, L⟩ : State) =
      ⟨⟨o + 11, r1, p1, m⟩, false, w + 11, L⟩ ∧
      r1 9 = m (-5) / (m (-3) + m (-3)) ∧ r1 18 = m (-5) / (m (-3) + m (-3)) - 1 ∧
      (∀ k, k % 3 ≠ 0 → r1 k = r k) ∧ (∀ k, k % 3 ≠ 0 → p1 k = p k) := by
    rw [hx]
    rw [xs_core R _ _ _ _ _ _ _ e0]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ e1]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self]
    rw [xs_core R _ _ _ _ _ _ _ e2]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self, h0, if_false]
    rw [xs_core R _ _ _ _ _ _ _ e3]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ e4]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self]
    rw [xs_core R _ _ _ _ _ _ _ e5]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ e6]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self]
    rw [xs_core R _ _ _ _ _ _ _ e7]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ e8]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ e9]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    rw [xs_core R _ _ _ _ _ _ _ e10]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    refine ⟨_, _, rfl, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · have : k ≠ 0 := by omega
      have : k ≠ 3 := by omega
      have : k ≠ 6 := by omega
      have : k ≠ 9 := by omega
      have : k ≠ 15 := by omega
      have : k ≠ 18 := by omega
      simp [Function.update_apply, *]
    · have : k ≠ 0 := by omega
      have : k ≠ 3 := by omega
      simp [Function.update_apply, *]
  obtain ⟨r1, p1, he, hr9, hr18, hr, hp⟩ := h11
  by_cases hle : m (-5) / (m (-3) + m (-3)) - 1 ≤ 0
  · refine ⟨12, r1, p1, by norm_num, ?_, by rw [if_pos hle, hr9], hr, hp⟩
    rw [Function.iterate_succ_apply', he, xs_core R _ _ _ _ _ _ _ e11]
    simp only [coreExec, hr18, hle, if_true]
  · refine ⟨13, Function.update r1 9 1, p1, le_rfl, ?_, by rw [if_neg hle]; simp,
      fun k hk => ?_, hp⟩
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', he,
        xs_core R _ _ _ _ _ _ _ e11]
      simp only [coreExec, hr18, hle, if_false]
      rw [xs_core R _ _ _ _ _ _ _ e12]
      simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    · have : k ≠ 9 := by omega
      simp [Function.update_apply, this, hr k hk]


lemma segD_pre2 (R : Program) (o : ℕ) (hD : ∀ k < 37, R[o + k]? = (segD o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (w L : ℕ) :
    ∃ r2 p2 m2, (step R)^[12] ⟨⟨o + 13, r, p, m⟩, false, w, L⟩ =
      ⟨⟨o + 25, r2, p2, m2⟩, false, w + 12, L⟩ ∧
      (∀ y, m2 y = if y = 2 then r 9 else if y = 0 then (p 1 : ℝ) - 2 else m y) ∧
      p2 3 = 4 ∧ p2 6 = -7 ∧ p2 9 = p 1 + p 1 - 2 ∧
      (∀ k, k % 3 ≠ 0 → r2 k = r k) ∧ (∀ k, k % 3 ≠ 0 → p2 k = p k) := by
  have e13 : R[o + 13]? = some (.ofPtr 18 1) := by rw [hD 13 (by norm_num)]; rfl
  have e14 : R[o + 14]? = some (.core (.const 21 2)) := by rw [hD 14 (by norm_num)]; rfl
  have e15 : R[o + 15]? = some (.core (.sub 18 18 21)) := by rw [hD 15 (by norm_num)]; rfl
  have e16 : R[o + 16]? = some (.core (.pset 0 0)) := by rw [hD 16 (by norm_num)]; rfl
  have e17 : R[o + 17]? = some (.core (.store 0 18)) := by rw [hD 17 (by norm_num)]; rfl
  have e18 : R[o + 18]? = some (.core (.pset 0 2)) := by rw [hD 18 (by norm_num)]; rfl
  have e19 : R[o + 19]? = some (.core (.store 0 9)) := by rw [hD 19 (by norm_num)]; rfl
  have e20 : R[o + 20]? = some (.core (.pset 3 4)) := by rw [hD 20 (by norm_num)]; rfl
  have e21 : R[o + 21]? = some (.core (.pset 6 (-7))) := by rw [hD 21 (by norm_num)]; rfl
  have e22 : R[o + 22]? = some (.core (.pset 15 2)) := by rw [hD 22 (by norm_num)]; rfl
  have e23 : R[o + 23]? = some (.padd 9 1 1) := by rw [hD 23 (by norm_num)]; rfl
  have e24 : R[o + 24]? = some (.psub 9 9 15) := by rw [hD 24 (by norm_num)]; rfl
  have hx : (step R)^[12] (⟨⟨o + 13, r, p, m⟩, false, w, L⟩ : State) = step R (step R (step R
      (step R (step R (step R (step R (step R (step R (step R (step R (step R
        ⟨⟨o + 13, r, p, m⟩, false, w, L⟩))))))))))) := rfl
  rw [hx]
  rw [xs_ofPtr R _ _ _ _ _ _ _ _ e13]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e14]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e15]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e16]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e17]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e18]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e19]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e20]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e21]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e22]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_padd R _ _ _ _ _ _ _ _ _ e23]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ e24]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  refine ⟨_, _, _, rfl, fun y => ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · simp [Function.update_apply]
  · have : k ≠ 18 := by omega
    have : k ≠ 21 := by omega
    simp [Function.update_apply, *]
  · have : k ≠ 0 := by omega
    have : k ≠ 3 := by omega
    have : k ≠ 6 := by omega
    have : k ≠ 9 := by omega
    have : k ≠ 15 := by omega
    simp [Function.update_apply, *]

lemma segD_body (R : Program) (o : ℕ) (hD : ∀ k < 37, R[o + k]? = (segD o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w L : ℕ) (hlt : ¬ p 9 ≤ p 3) :
    ∃ r' p', (step R)^[8] ⟨⟨o + 25, r, p, M⟩, false, w, L⟩ =
      ⟨⟨o + 25, r', p', Function.update M (p 3) (M (p 6))⟩, false, w + 8, L⟩ ∧
      p' 3 = p 3 + 2 ∧ p' 6 = p 6 - 2 ∧ p' 9 = p 9 ∧
      (∀ k, k % 3 ≠ 0 → r' k = r k) ∧ (∀ k, k % 3 ≠ 0 → p' k = p k) := by
  have e25 : R[o + 25]? = some (.core (.pjle 9 3 (o + 37))) := by rw [hD 25 (by norm_num)]; rfl
  have e26 : R[o + 26]? = some (.core (.load 24 6)) := by rw [hD 26 (by norm_num)]; rfl
  have e27 : R[o + 27]? = some (.core (.store 3 24)) := by rw [hD 27 (by norm_num)]; rfl
  have e28 : R[o + 28]? = some (.core (.pinc 3)) := by rw [hD 28 (by norm_num)]; rfl
  have e29 : R[o + 29]? = some (.core (.pinc 3)) := by rw [hD 29 (by norm_num)]; rfl
  have e30 : R[o + 30]? = some (.core (.pdec 6)) := by rw [hD 30 (by norm_num)]; rfl
  have e31 : R[o + 31]? = some (.core (.pdec 6)) := by rw [hD 31 (by norm_num)]; rfl
  have e32 : R[o + 32]? = some (.core (.pjle 0 0 (o + 25))) := by rw [hD 32 (by norm_num)]; rfl
  have hx : (step R)^[8] (⟨⟨o + 25, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R
      (step R (step R (step R (step R (step R ⟨⟨o + 25, r, p, M⟩, false, w, L⟩))))))) := rfl
  rw [hx]
  rw [xs_core R _ _ _ _ _ _ _ e25]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, hlt, if_false]
  rw [xs_core R _ _ _ _ _ _ _ e26]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e27]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_self]
  rw [xs_core R _ _ _ _ _ _ _ e28]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e29]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e30]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e31]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
  rw [xs_core R _ _ _ _ _ _ _ e32]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, le_refl, if_true]
  refine ⟨_, _, rfl, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  · simp [Function.update_apply]; ring
  · simp [Function.update_apply]; ring
  · simp [Function.update_apply]
  · have : k ≠ 24 := by omega
    simp [Function.update_apply, *]
  · have : k ≠ 3 := by omega
    have : k ≠ 6 := by omega
    simp [Function.update_apply, *]

noncomputable def memD (M1 : ℤ → ℝ) (v : ℤ → ℝ) (c : ℤ) (y : ℤ) : ℝ :=
  if 4 ≤ y ∧ y < 4 + 2 * c ∧ y % 2 = 0 then v ((y - 4) / 2) else M1 y

lemma segD_loop (R : Program) (o : ℕ) (hD : ∀ k < 37, R[o + k]? = (segD o)[k]?)
    (M1 v : ℤ → ℝ) (N : ℕ) (hv : ∀ t : ℕ, t < N → M1 (-7 - 2 * (t : ℤ)) = v t) (L : ℕ) :
    ∀ (k c : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), c + k = N →
      p 3 = 4 + 2 * (c : ℤ) → p 6 = -7 - 2 * (c : ℤ) → p 9 = 4 + 2 * (N : ℤ) →
      ∃ r' p', (step R)^[8 * k + 1] ⟨⟨o + 25, r, p, memD M1 v c⟩, false, w, L⟩ =
        ⟨⟨o + 37, r', p', memD M1 v N⟩, false, w + 8 * k + 1, L⟩ ∧
        (∀ k, k % 3 ≠ 0 → r' k = r k) ∧ (∀ k, k % 3 ≠ 0 → p' k = p k) := by
  have e25 : R[o + 25]? = some (.core (.pjle 9 3 (o + 37))) := by rw [hD 25 (by norm_num)]; rfl
  intro k
  induction k with
  | zero =>
    intro c r p w hc h3 h6 h9
    refine ⟨r, p, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simp only [Nat.mul_zero, Nat.zero_add, Function.iterate_one]
    rw [xs_core R _ _ _ _ _ _ _ e25]
    have : p 9 ≤ p 3 := by rw [h9, h3]; omega
    simp only [coreExec, this, if_true]
    rw [show c = N by omega]
  | succ k ih =>
    intro c r p w hc h3 h6 h9
    obtain ⟨r1, p1, he, g3, g6, g9, gr, gp⟩ :=
      segD_body R o hD r p (memD M1 v c) w L (by rw [h9, h3]; omega)
    have hM : Function.update (memD M1 v c) (p 3) (memD M1 v c (p 6)) = memD M1 v ((c + 1 : ℕ) : ℤ) := by
      have hsrc : memD M1 v c (p 6) = v c := by
        simp only [memD, h6]; rw [if_neg (by omega)]; exact hv c (by omega)
      rw [hsrc, h3]
      funext y
      simp only [Function.update_apply, memD]
      push_cast
      split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)
    rw [show 8 * (k + 1) + 1 = (8 * k + 1) + 8 by ring, Function.iterate_add_apply, he, hM]
    obtain ⟨r', p', he', hr', hp'⟩ := ih (c + 1) r1 p1 (w + 8) (by omega)
      (by rw [g3, h3]; push_cast; ring) (by rw [g6, h6]; push_cast; ring) (by rw [g9, h9])
    refine ⟨r', p', ?_, fun k hk => by rw [hr' k hk, gr k hk], fun k hk => by rw [hp' k hk, gp k hk]⟩
    rw [he', show w + 8 + 8 * k + 1 = w + 8 * (k + 1) + 1 by ring]


noncomputable def epsOf (Λ g : ℝ) : ℝ := if g / (Λ + Λ) - 1 ≤ 0 then g / (Λ + Λ) else 1

lemma segD_yes (R : Program) (o : ℕ) (hD : ∀ k < 37, R[o + k]? = (segD o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (w L : ℕ) (h0 : ¬ m (-1) ≤ 0) (n : ℕ)
    (hp1 : p 1 = 2 * (n : ℤ) + 3) (v : ℤ → ℝ)
    (hv : ∀ t : ℕ, t < 2 * n → m (-7 - 2 * (t : ℤ)) = v t) :
    ∃ j r' p' m', j ≤ 16 * n + 26 ∧ (step R)^[j] ⟨⟨o, r, p, m⟩, false, w, L⟩ =
      ⟨⟨o + 37, r', p', m'⟩, false, w + j, L⟩ ∧
      (∀ k, k % 3 ≠ 0 → r' k = r k) ∧ (∀ k, k % 3 ≠ 0 → p' k = p k) ∧
      (∀ y, m' y = memD (fun y => if y = 2 then epsOf (m (-3)) (m (-5)) else
        if y = 0 then (2 * n + 1 : ℝ) else m y) v ((2 * n : ℕ) : ℤ) y) := by
  obtain ⟨k1, r1, p1, hk1, he1, hr19, hr1, hp1'⟩ := segD_pre1 R o hD r p m w L h0
  obtain ⟨r2, p2, m2, he2, hm2, g3, g6, g9, gr, gp⟩ := segD_pre2 R o hD r1 p1 m (w + k1) L
  set M1 : ℤ → ℝ := fun y => if y = 2 then epsOf (m (-3)) (m (-5)) else
        if y = 0 then (2 * n + 1 : ℝ) else m y with hM1
  have hm2' : m2 = memD M1 v (0 : ℕ) := by
    funext y
    rw [hm2]
    simp only [memD, M1, epsOf]
    have hc : ¬ (4 ≤ y ∧ y < 4 + 2 * ((0 : ℕ) : ℤ) ∧ y % 2 = 0) := by omega
    rw [if_neg hc]
    by_cases h2 : y = 2
    · subst h2; simp [hr19, epsOf]
    · by_cases h0' : y = 0
      · subst h0'; simp [hp1' 1 (by norm_num), hp1]; ring
      · simp [h2, h0']
  obtain ⟨r3, p3, he3, hr3, hp3⟩ := segD_loop R o hD M1 v (2 * n) (by
      intro t ht
      simp only [M1]
      rw [if_neg (by omega), if_neg (by omega)]
      exact hv t ht) L (2 * n) 0 r2 p2 (w + k1 + 12) (by omega)
    (by rw [g3]; simp) (by rw [g6]; simp) (by rw [g9, hp1' 1 (by norm_num), hp1]; push_cast; ring)
  refine ⟨8 * (2 * n) + 1 + 12 + k1, r3, p3, memD M1 v ((2 * n : ℕ) : ℤ), by omega, ?_,
    fun k hk => by rw [hr3 k hk, gr k hk, hr1 k hk],
    fun k hk => by rw [hp3 k hk, gp k hk, hp1' k hk], fun y => rfl⟩
  rw [Function.iterate_add_apply, Function.iterate_add_apply, he1, he2, hm2', he3]
  congr 1; ring

def segF (o : ℕ) : List Instr :=
  [.core (.const 0 0),
   .core (.pset 27 (-2)),
   .core (.pset 30 (-7)),
   .padd 36 2 2,
   .psub 33 30 36,
   .core (.pset 3 0),
   .core (.pjle 2 3 (o + 44)),
   .core (.pset 6 0),
   .core (.pjle 2 6 (o + 42)),
   .padd 39 3 3,
   .psub 42 27 39,
   .core (.load 3 42),
   .psub 42 30 39,
   .core (.load 6 42),
   .psub 42 33 39,
   .core (.load 9 42),
   .padd 39 6 6,
   .psub 42 27 39,
   .core (.load 12 42),
   .psub 42 30 39,
   .core (.load 15 42),
   .psub 42 33 39,
   .core (.load 18 42),
   .core (.sub 21 3 12),
   .core (.jle 21 (o + 26)),
   .core (.pjle 0 0 (o + 40)),
   .core (.sub 21 12 3),
   .core (.jle 21 (o + 29)),
   .core (.pjle 0 0 (o + 40)),
   .core (.mul 24 9 15),
   .core (.mul 27 18 6),
   .core (.sub 21 24 27),
   .core (.jle 21 (o + 34)),
   .core (.pjle 0 0 (o + 40)),
   .core (.sub 21 27 24),
   .core (.jle 21 (o + 37)),
   .core (.pjle 0 0 (o + 39)),
   .core (.pjle 6 3 (o + 39)),
   .core (.pjle 0 0 (o + 40)),
   .core (.add 0 0 24),
   .core (.pinc 6),
   .core (.pjle 0 0 (o + 8)),
   .core (.pinc 3),
   .core (.pjle 0 0 (o + 6)),
   .core (.pset 42 (-3)),
   .core (.load 3 42),
   .core (.pset 42 (-5)),
   .core (.load 6 42),
   .core (.add 9 3 6),
   .core (.sub 9 9 0),
   .core (.pset 0 (-1)),
   .core (.jle 9 (o + 56)),
   .core (.const 12 1),
   .core (.store 0 12),
   .core (.pset 0 1),
   .halt,
   .core (.const 12 0),
   .core (.store 0 12),
   .core (.pset 0 1),
   .halt]

lemma segF_load (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w L : ℕ) (hlt : ¬ p 2 ≤ p 6) :
    ∃ r' p', (step R)^[16] ⟨⟨o + 8, r, p, M⟩, false, w, L⟩ =
      ⟨⟨o + 24, r', p', M⟩, false, w + 16, L⟩ ∧
      r' 21 = M (p 27 - (p 3 + p 3)) - M (p 27 - (p 6 + p 6)) ∧
      r' 3 = M (p 27 - (p 3 + p 3)) ∧ r' 6 = M (p 30 - (p 3 + p 3)) ∧
      r' 9 = M (p 33 - (p 3 + p 3)) ∧ r' 12 = M (p 27 - (p 6 + p 6)) ∧
      r' 15 = M (p 30 - (p 6 + p 6)) ∧ r' 18 = M (p 33 - (p 6 + p 6)) ∧ r' 0 = r 0 ∧
      (∀ k, k % 3 ≠ 0 → r' k = r k) ∧
      (∀ k, k = 2 ∨ k = 3 ∨ k = 6 ∨ k = 27 ∨ k = 30 ∨ k = 33 ∨ k % 3 ≠ 0 → p' k = p k) := by

  have f8 : R[o + 8]? = some (.core (.pjle 2 6 (o + 42))) := by rw [hF 8 (by norm_num)]; rfl
  have f9 : R[o + 9]? = some (.padd 39 3 3) := by rw [hF 9 (by norm_num)]; rfl
  have f10 : R[o + 10]? = some (.psub 42 27 39) := by rw [hF 10 (by norm_num)]; rfl
  have f11 : R[o + 11]? = some (.core (.load 3 42)) := by rw [hF 11 (by norm_num)]; rfl
  have f12 : R[o + 12]? = some (.psub 42 30 39) := by rw [hF 12 (by norm_num)]; rfl
  have f13 : R[o + 13]? = some (.core (.load 6 42)) := by rw [hF 13 (by norm_num)]; rfl
  have f14 : R[o + 14]? = some (.psub 42 33 39) := by rw [hF 14 (by norm_num)]; rfl
  have f15 : R[o + 15]? = some (.core (.load 9 42)) := by rw [hF 15 (by norm_num)]; rfl
  have f16 : R[o + 16]? = some (.padd 39 6 6) := by rw [hF 16 (by norm_num)]; rfl
  have f17 : R[o + 17]? = some (.psub 42 27 39) := by rw [hF 17 (by norm_num)]; rfl
  have f18 : R[o + 18]? = some (.core (.load 12 42)) := by rw [hF 18 (by norm_num)]; rfl
  have f19 : R[o + 19]? = some (.psub 42 30 39) := by rw [hF 19 (by norm_num)]; rfl
  have f20 : R[o + 20]? = some (.core (.load 15 42)) := by rw [hF 20 (by norm_num)]; rfl
  have f21 : R[o + 21]? = some (.psub 42 33 39) := by rw [hF 21 (by norm_num)]; rfl
  have f22 : R[o + 22]? = some (.core (.load 18 42)) := by rw [hF 22 (by norm_num)]; rfl
  have f23 : R[o + 23]? = some (.core (.sub 21 3 12)) := by rw [hF 23 (by norm_num)]; rfl
  have hx : (step R)^[16] (⟨⟨o + 8, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (⟨⟨o + 8, r, p, M⟩, false, w, L⟩ : State)))))))))))))))) := rfl
  rw [hx]
  rw [xs_core R _ _ _ _ _ _ _ f8]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_padd R _ _ _ _ _ _ _ _ _ f9]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ f10]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f11]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ f12]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f13]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ f14]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f15]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_padd R _ _ _ _ _ _ _ _ _ f16]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ f17]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f18]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ f19]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f20]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_psub R _ _ _ _ _ _ _ _ _ f21]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f22]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  rw [xs_core R _ _ _ _ _ _ _ f23]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hlt]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_⟩
  all_goals (try simp)
  · have : k ≠ 3 := by omega
    have : k ≠ 6 := by omega
    have : k ≠ 9 := by omega
    have : k ≠ 12 := by omega
    have : k ≠ 15 := by omega
    have : k ≠ 18 := by omega
    have : k ≠ 21 := by omega
    simp [*]
  · have : k ≠ 39 := by omega
    have : k ≠ 42 := by omega
    simp [*]

noncomputable def fcond (a3 a6 a9 a12 a15 a18 : ℝ) (b6 b3 : ℤ) : Prop :=
  a3 = a12 ∧ (a9 * a15 < a18 * a6 ∨ (a9 * a15 = a18 * a6 ∧ b6 ≤ b3))

lemma segF_dec (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w L : ℕ) (h21 : r 21 = r 3 - r 12) :
    ∃ k r', k ≤ 16 ∧ (step R)^[k] ⟨⟨o + 24, r, p, M⟩, false, w, L⟩ =
      ⟨⟨o + 40, r', p, M⟩, false, w + k, L⟩ ∧
      r' 0 = (if r 3 = r 12 ∧ (r 9 * r 15 < r 18 * r 6 ∨ (r 9 * r 15 = r 18 * r 6 ∧ p 6 ≤ p 3))
        then r 0 + r 9 * r 15 else r 0) ∧
      (∀ k, k % 3 ≠ 0 → r' k = r k) := by

  have f24 : R[o + 24]? = some (.core (.jle 21 (o + 26))) := by rw [hF 24 (by norm_num)]; rfl
  have f25 : R[o + 25]? = some (.core (.pjle 0 0 (o + 40))) := by rw [hF 25 (by norm_num)]; rfl
  have f26 : R[o + 26]? = some (.core (.sub 21 12 3)) := by rw [hF 26 (by norm_num)]; rfl
  have f27 : R[o + 27]? = some (.core (.jle 21 (o + 29))) := by rw [hF 27 (by norm_num)]; rfl
  have f28 : R[o + 28]? = some (.core (.pjle 0 0 (o + 40))) := by rw [hF 28 (by norm_num)]; rfl
  have f29 : R[o + 29]? = some (.core (.mul 24 9 15)) := by rw [hF 29 (by norm_num)]; rfl
  have f30 : R[o + 30]? = some (.core (.mul 27 18 6)) := by rw [hF 30 (by norm_num)]; rfl
  have f31 : R[o + 31]? = some (.core (.sub 21 24 27)) := by rw [hF 31 (by norm_num)]; rfl
  have f32 : R[o + 32]? = some (.core (.jle 21 (o + 34))) := by rw [hF 32 (by norm_num)]; rfl
  have f33 : R[o + 33]? = some (.core (.pjle 0 0 (o + 40))) := by rw [hF 33 (by norm_num)]; rfl
  have f34 : R[o + 34]? = some (.core (.sub 21 27 24)) := by rw [hF 34 (by norm_num)]; rfl
  have f35 : R[o + 35]? = some (.core (.jle 21 (o + 37))) := by rw [hF 35 (by norm_num)]; rfl
  have f36 : R[o + 36]? = some (.core (.pjle 0 0 (o + 39))) := by rw [hF 36 (by norm_num)]; rfl
  have f37 : R[o + 37]? = some (.core (.pjle 6 3 (o + 39))) := by rw [hF 37 (by norm_num)]; rfl
  have f38 : R[o + 38]? = some (.core (.pjle 0 0 (o + 40))) := by rw [hF 38 (by norm_num)]; rfl
  have f39 : R[o + 39]? = some (.core (.add 0 0 24)) := by rw [hF 39 (by norm_num)]; rfl
  by_cases c1 : r 3 - r 12 ≤ 0
  · by_cases c2 : r 12 - r 3 ≤ 0
    · by_cases c3 : r 9 * r 15 - r 18 * r 6 ≤ 0
      · by_cases c4 : r 18 * r 6 - r 9 * r 15 ≤ 0
        · by_cases c5 : p 6 ≤ p 3
          · refine ⟨11, ?_⟩
            rw [show (step R)^[11] (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State))))))))))) from rfl]
            rw [xs_core R _ _ _ _ _ _ _ f24]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f26]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f27]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f29]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f30]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f31]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f32]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f34]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f35]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f37]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f39]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            refine ⟨_, by norm_num, rfl, ?_, fun k hk => ?_⟩
            · rw [if_pos (by refine ⟨by linarith, ?_⟩; first | exact Or.inl (by linarith) | exact Or.inr ⟨by linarith, by first | exact c5 | trivial⟩)]
              try simp
            · have : k ≠ 21 := by omega
              have : k ≠ 24 := by omega
              have : k ≠ 27 := by omega
              have : k ≠ 0 := by omega
              simp [*]
          · refine ⟨11, ?_⟩
            rw [show (step R)^[11] (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State))))))))))) from rfl]
            rw [xs_core R _ _ _ _ _ _ _ f24]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f26]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f27]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f29]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f30]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f31]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f32]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f34]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f35]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f37]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            rw [xs_core R _ _ _ _ _ _ _ f38]
            simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4, c5]
            refine ⟨_, by norm_num, rfl, ?_, fun k hk => ?_⟩
            · rw [if_neg (by intro hc; rcases hc with ⟨hc1, hc2 | ⟨hc2, hc3⟩⟩ <;> first | linarith | exact c5 hc3 | exact hc3)]
              try simp
            · have : k ≠ 21 := by omega
              have : k ≠ 24 := by omega
              have : k ≠ 27 := by omega
              have : k ≠ 0 := by omega
              simp [*]
        · refine ⟨11, ?_⟩
          rw [show (step R)^[11] (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State))))))))))) from rfl]
          rw [xs_core R _ _ _ _ _ _ _ f24]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f26]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f27]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f29]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f30]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f31]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f32]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f34]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f35]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f36]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          rw [xs_core R _ _ _ _ _ _ _ f39]
          simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3, c4]
          refine ⟨_, by norm_num, rfl, ?_, fun k hk => ?_⟩
          · rw [if_pos (by refine ⟨by linarith, ?_⟩; first | exact Or.inl (by linarith) | exact Or.inr ⟨by linarith, by first | exact c5 | trivial⟩)]
            try simp
          · have : k ≠ 21 := by omega
            have : k ≠ 24 := by omega
            have : k ≠ 27 := by omega
            have : k ≠ 0 := by omega
            simp [*]
      · refine ⟨8, ?_⟩
        rw [show (step R)^[8] (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (step R (step R (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State)))))))) from rfl]
        rw [xs_core R _ _ _ _ _ _ _ f24]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f26]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f27]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f29]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f30]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f31]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f32]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        rw [xs_core R _ _ _ _ _ _ _ f33]
        simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2, c3]
        refine ⟨_, by norm_num, rfl, ?_, fun k hk => ?_⟩
        · rw [if_neg (by intro hc; rcases hc with ⟨hc1, hc2 | ⟨hc2, hc3⟩⟩ <;> first | linarith | exact c5 hc3 | exact hc3)]
          try simp
        · have : k ≠ 21 := by omega
          have : k ≠ 24 := by omega
          have : k ≠ 27 := by omega
          have : k ≠ 0 := by omega
          simp [*]
    · refine ⟨4, ?_⟩
      rw [show (step R)^[4] (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State)))) from rfl]
      rw [xs_core R _ _ _ _ _ _ _ f24]
      simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2]
      rw [xs_core R _ _ _ _ _ _ _ f26]
      simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2]
      rw [xs_core R _ _ _ _ _ _ _ f27]
      simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2]
      rw [xs_core R _ _ _ _ _ _ _ f28]
      simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1, c2]
      refine ⟨_, by norm_num, rfl, ?_, fun k hk => ?_⟩
      · rw [if_neg (by intro hc; rcases hc with ⟨hc1, hc2 | ⟨hc2, hc3⟩⟩ <;> first | linarith | exact c5 hc3 | exact hc3)]
        try simp
      · have : k ≠ 21 := by omega
        have : k ≠ 24 := by omega
        have : k ≠ 27 := by omega
        have : k ≠ 0 := by omega
        simp [*]
  · refine ⟨2, ?_⟩
    rw [show (step R)^[2] (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State) = step R (step R (⟨⟨o + 24, r, p, M⟩, false, w, L⟩ : State)) from rfl]
    rw [xs_core R _ _ _ _ _ _ _ f24]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1]
    rw [xs_core R _ _ _ _ _ _ _ f25]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, h21, c1]
    refine ⟨_, by norm_num, rfl, ?_, fun k hk => ?_⟩
    · rw [if_neg (by intro hc; rcases hc with ⟨hc1, hc2 | ⟨hc2, hc3⟩⟩ <;> first | linarith | exact c5 hc3 | exact hc3)]
      try simp
    · have : k ≠ 21 := by omega
      have : k ≠ 24 := by omega
      have : k ≠ 27 := by omega
      have : k ≠ 0 := by omega
      simp [*]


noncomputable def fval (M : ℤ → ℝ) (c27 c30 c33 : ℤ) (j i : ℤ) : ℝ :=
  if M (c27 - (j + j)) = M (c27 - (i + i)) ∧
      (M (c33 - (j + j)) * M (c30 - (i + i)) < M (c33 - (i + i)) * M (c30 - (j + j)) ∨
        (M (c33 - (j + j)) * M (c30 - (i + i)) = M (c33 - (i + i)) * M (c30 - (j + j)) ∧ i ≤ j))
  then M (c33 - (j + j)) * M (c30 - (i + i)) else 0

/-- the pointer registers that segment F keeps fixed inside its loops -/
def FixF (p p' : ℕ → ℤ) : Prop :=
  p' 2 = p 2 ∧ p' 27 = p 27 ∧ p' 30 = p 30 ∧ p' 33 = p 33 ∧ ∀ k, k % 3 ≠ 0 → p' k = p k

lemma segF_iter (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w L : ℕ) (hlt : ¬ p 2 ≤ p 6) :
    ∃ k r' p', k ≤ 34 ∧ (step R)^[k] ⟨⟨o + 8, r, p, M⟩, false, w, L⟩ =
      ⟨⟨o + 8, r', p', M⟩, false, w + k, L⟩ ∧
      r' 0 = r 0 + fval M (p 27) (p 30) (p 33) (p 3) (p 6) ∧ p' 6 = p 6 + 1 ∧ p' 3 = p 3 ∧
      FixF p p' ∧ (∀ k, k % 3 ≠ 0 → r' k = r k) := by
  have f40 : R[o + 40]? = some (.core (.pinc 6)) := by rw [hF 40 (by norm_num)]; rfl
  have f41 : R[o + 41]? = some (.core (.pjle 0 0 (o + 8))) := by rw [hF 41 (by norm_num)]; rfl
  obtain ⟨r1, p1, he1, g21, g3, g6, g9, g12, g15, g18, g0, gr, gp⟩ :=
    segF_load R o hF r p M w L hlt
  obtain ⟨k2, r2, hk2, he2, h0, hr2⟩ := segF_dec R o hF r1 p1 M (w + 16) L (by rw [g21, g3, g12])
  refine ⟨2 + k2 + 16, r2, Function.update p1 6 (p1 6 + 1), by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, he1, he2]
    show step R (step R _) = _
    rw [xs_core R _ _ _ _ _ _ _ f40]
    simp only [coreExec]
    rw [xs_core R _ _ _ _ _ _ _ f41]
    simp only [coreExec, le_refl, if_true, Function.update_self]
    congr 1; omega
  · rw [h0, g3, g6, g9, g12, g15, g18, g0]
    simp only [gp 3 (by simp), gp 6 (by simp)]
    unfold fval
    split_ifs <;> simp
  · simp [gp 6 (by simp)]
  · simp [gp 3 (by simp)]
  · refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_⟩
    · simp [gp 2 (by simp)]
    · simp [gp 27 (by simp)]
    · simp [gp 30 (by simp)]
    · simp [gp 33 (by simp)]
    · have : k ≠ 6 := by omega
      simp [this, gp k (by simp [hk])]
  · intro k hk; rw [hr2 k hk, gr k hk]


lemma FixF_trans {p p1 p2 : ℕ → ℤ} (h1 : FixF p p1) (h2 : FixF p1 p2) : FixF p p2 :=
  ⟨by rw [h2.1, h1.1], by rw [h2.2.1, h1.2.1], by rw [h2.2.2.1, h1.2.2.1],
    by rw [h2.2.2.2.1, h1.2.2.2.1], fun k hk => by rw [h2.2.2.2.2 k hk, h1.2.2.2.2 k hk]⟩

lemma segF_inner (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (M : ℤ → ℝ) (L : ℕ) :
    ∀ (c : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), p 2 = p 6 + c →
      ∃ k r' p', k ≤ 35 * c + 1 ∧ (step R)^[k] ⟨⟨o + 8, r, p, M⟩, false, w, L⟩ =
        ⟨⟨o + 42, r', p', M⟩, false, w + k, L⟩ ∧
        r' 0 = r 0 + ∑ t ∈ Finset.range c, fval M (p 27) (p 30) (p 33) (p 3) (p 6 + t) ∧
        p' 3 = p 3 ∧ FixF p p' ∧ (∀ k, k % 3 ≠ 0 → r' k = r k) := by
  have f8 : R[o + 8]? = some (.core (.pjle 2 6 (o + 42))) := by rw [hF 8 (by norm_num)]; rfl
  intro c
  induction c with
  | zero =>
    intro r p w h2
    refine ⟨1, r, p, by norm_num, ?_, by simp, rfl, ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun _ _ => rfl⟩
    rw [Function.iterate_one, xs_core R _ _ _ _ _ _ _ f8]
    have : p 2 ≤ p 6 := by rw [h2]; simp
    simp only [coreExec, this, if_true]
  | succ c ih =>
    intro r p w h2
    obtain ⟨k1, r1, p1, hk1, he1, h0, g6, g3, gF, gr⟩ :=
      segF_iter R o hF r p M w L (by rw [h2]; push_cast; omega)
    obtain ⟨k2, r2, p2, hk2, he2, h0', g3', gF', gr'⟩ := ih r1 p1 (w + k1)
      (by rw [gF.1, g6, h2]; push_cast; ring)
    refine ⟨k2 + k1, r2, p2, by omega, ?_, ?_, by rw [g3', g3], FixF_trans gF gF',
      fun k hk => by rw [gr' k hk, gr k hk]⟩
    · rw [Function.iterate_add_apply, he1, he2, Nat.add_assoc, Nat.add_comm k1 k2]
    · rw [h0', h0, Finset.sum_range_succ', g6, g3, gF.2.1, gF.2.2.1, gF.2.2.2.1]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      have : ∀ t : ℕ, p 6 + 1 + (t : ℤ) = p 6 + ((t : ℤ) + 1) := fun t => by ring
      simp only [this]
      ring

lemma segF_outer (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (M : ℤ → ℝ) (L n : ℕ) :
    ∀ (c : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), p 2 = n → p 2 = p 3 + c →
      ∃ k r' p', k ≤ (35 * n + 5) * c + 1 ∧ (step R)^[k] ⟨⟨o + 6, r, p, M⟩, false, w, L⟩ =
        ⟨⟨o + 44, r', p', M⟩, false, w + k, L⟩ ∧
        r' 0 = r 0 + ∑ t ∈ Finset.range c, ∑ i ∈ Finset.range n,
          fval M (p 27) (p 30) (p 33) (p 3 + t) i ∧
        FixF p p' ∧ (∀ k, k % 3 ≠ 0 → r' k = r k) := by
  have f6 : R[o + 6]? = some (.core (.pjle 2 3 (o + 44))) := by rw [hF 6 (by norm_num)]; rfl
  have f7 : R[o + 7]? = some (.core (.pset 6 0)) := by rw [hF 7 (by norm_num)]; rfl
  have f42 : R[o + 42]? = some (.core (.pinc 3)) := by rw [hF 42 (by norm_num)]; rfl
  have f43 : R[o + 43]? = some (.core (.pjle 0 0 (o + 6))) := by rw [hF 43 (by norm_num)]; rfl
  intro c
  induction c with
  | zero =>
    intro r p w hn h2
    refine ⟨1, r, p, by norm_num, ?_, by simp, ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
      fun _ _ => rfl⟩
    rw [Function.iterate_one, xs_core R _ _ _ _ _ _ _ f6]
    have : p 2 ≤ p 3 := by rw [h2]; simp
    simp only [coreExec, this, if_true]
  | succ c ih =>
    intro r p w hn h2
    have hlt : ¬ p 2 ≤ p 3 := by rw [h2]; push_cast; omega
    have hpre : (step R)^[2] (⟨⟨o + 6, r, p, M⟩, false, w, L⟩ : State) =
        ⟨⟨o + 8, r, Function.update p 6 0, M⟩, false, w + 2, L⟩ := by
      show step R (step R _) = _
      rw [xs_core R _ _ _ _ _ _ _ f6]
      simp only [coreExec, hlt, if_false]
      rw [xs_core R _ _ _ _ _ _ _ f7]
      simp only [coreExec, Nat.add_assoc, Nat.reduceAdd]
    obtain ⟨k1, r1, p1, hk1, he1, h0, g3, gF, gr⟩ := segF_inner R o hF M L n r
      (Function.update p 6 0) (w + 2) (by simp [hn])
    have hpost : (step R)^[2] (⟨⟨o + 42, r1, p1, M⟩, false, w + 2 + k1, L⟩ : State) =
        ⟨⟨o + 6, r1, Function.update p1 3 (p1 3 + 1), M⟩, false, w + 2 + k1 + 2, L⟩ := by
      show step R (step R _) = _
      rw [xs_core R _ _ _ _ _ _ _ f42]
      simp only [coreExec]
      rw [xs_core R _ _ _ _ _ _ _ f43]
      simp only [coreExec, le_refl, if_true]
    have gF2 : FixF p (Function.update p1 3 (p1 3 + 1)) := by
      have hF1 : FixF p (Function.update p 6 0) :=
        ⟨by simp, by simp, by simp, by simp, fun k hk => by
          have : k ≠ 6 := by omega
          simp [this]⟩
      have hF2 : FixF p1 (Function.update p1 3 (p1 3 + 1)) :=
        ⟨by simp, by simp, by simp, by simp, fun k hk => by
          have : k ≠ 3 := by omega
          simp [this]⟩
      exact FixF_trans (FixF_trans hF1 gF) hF2
    have g3' : (Function.update p1 3 (p1 3 + 1)) 3 = p 3 + 1 := by simp [g3]
    obtain ⟨k2, r2, p2, hk2, he2, h0', gF', gr'⟩ := ih r1 (Function.update p1 3 (p1 3 + 1))
      (w + 2 + k1 + 2) (by rw [gF2.1, hn]) (by rw [gF2.1, g3', h2]; push_cast; ring)
    refine ⟨k2 + 2 + k1 + 2, r2, p2, ?_, ?_, ?_, FixF_trans gF2 gF', ?_⟩
    · have : (35 * n + 5) * (c + 1) + 1 = ((35 * n + 5) * c + 1) + (35 * n + 1) + 4 := by ring
      omega
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
        hpre, he1, hpost, he2]
      congr 1; omega
    · rw [h0', h0, Finset.sum_range_succ', gF2.2.1, gF2.2.2.1, gF2.2.2.2.1, g3']
      simp only [Function.update_apply, Nat.reduceEqDiff, reduceIte, Nat.cast_zero, zero_add,
        add_zero, Nat.cast_add, Nat.cast_one]
      have : ∀ t : ℕ, p 3 + 1 + (t : ℤ) = p 3 + ((t : ℤ) + 1) := fun t => by ring
      simp only [this]
      ring
    · intro k hk; rw [gr' k hk, gr k hk]

lemma segF_end (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w L : ℕ) :
    ((step R)^[12] ⟨⟨o + 44, r, p, M⟩, false, w, L⟩).halted = true ∧
    outputOf ((step R)^[12] ⟨⟨o + 44, r, p, M⟩, false, w, L⟩) =
      [if M (-3) + M (-5) - r 0 ≤ 0 then 0 else 1] := by
  have f44 : R[o + 44]? = some (.core (.pset 42 (-3))) := by rw [hF 44 (by norm_num)]; rfl
  have f45 : R[o + 45]? = some (.core (.load 3 42)) := by rw [hF 45 (by norm_num)]; rfl
  have f46 : R[o + 46]? = some (.core (.pset 42 (-5))) := by rw [hF 46 (by norm_num)]; rfl
  have f47 : R[o + 47]? = some (.core (.load 6 42)) := by rw [hF 47 (by norm_num)]; rfl
  have f48 : R[o + 48]? = some (.core (.add 9 3 6)) := by rw [hF 48 (by norm_num)]; rfl
  have f49 : R[o + 49]? = some (.core (.sub 9 9 0)) := by rw [hF 49 (by norm_num)]; rfl
  have f50 : R[o + 50]? = some (.core (.pset 0 (-1))) := by rw [hF 50 (by norm_num)]; rfl
  have f51 : R[o + 51]? = some (.core (.jle 9 (o + 56))) := by rw [hF 51 (by norm_num)]; rfl
  have f52 : R[o + 52]? = some (.core (.const 12 1)) := by rw [hF 52 (by norm_num)]; rfl
  have f53 : R[o + 53]? = some (.core (.store 0 12)) := by rw [hF 53 (by norm_num)]; rfl
  have f54 : R[o + 54]? = some (.core (.pset 0 1)) := by rw [hF 54 (by norm_num)]; rfl
  have f55 : R[o + 55]? = some (.halt) := by rw [hF 55 (by norm_num)]; rfl
  have f56 : R[o + 56]? = some (.core (.const 12 0)) := by rw [hF 56 (by norm_num)]; rfl
  have f57 : R[o + 57]? = some (.core (.store 0 12)) := by rw [hF 57 (by norm_num)]; rfl
  have f58 : R[o + 58]? = some (.core (.pset 0 1)) := by rw [hF 58 (by norm_num)]; rfl
  have f59 : R[o + 59]? = some (.halt) := by rw [hF 59 (by norm_num)]; rfl
  rw [show (step R)^[12] (⟨⟨o + 44, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (step R (⟨⟨o + 44, r, p, M⟩, false, w, L⟩ : State)))))))))))) from rfl]
  rw [xs_core R _ _ _ _ _ _ _ f44]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  rw [xs_core R _ _ _ _ _ _ _ f45]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  rw [xs_core R _ _ _ _ _ _ _ f46]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  rw [xs_core R _ _ _ _ _ _ _ f47]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  rw [xs_core R _ _ _ _ _ _ _ f48]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  rw [xs_core R _ _ _ _ _ _ _ f49]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  rw [xs_core R _ _ _ _ _ _ _ f50]
  simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
  by_cases hc : M (-3) + M (-5) - r 0 ≤ 0
  · rw [if_pos hc]
    rw [xs_core R _ _ _ _ _ _ _ f51]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_core R _ _ _ _ _ _ _ f56]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_core R _ _ _ _ _ _ _ f57]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_core R _ _ _ _ _ _ _ f58]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_halt R _ _ _ _ _ _ f59]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    simp [outputOf]
  · rw [if_neg hc]
    rw [xs_core R _ _ _ _ _ _ _ f51]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_core R _ _ _ _ _ _ _ f52]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_core R _ _ _ _ _ _ _ f53]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_core R _ _ _ _ _ _ _ f54]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    rw [xs_halt R _ _ _ _ _ _ f55]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl, hc]
    simp [outputOf]

lemma segF_spec (R : Program) (o : ℕ) (hF : ∀ k < 60, R[o + k]? = (segF o)[k]?)
    (r : ℕ → ℝ) (p : ℕ → ℤ) (M : ℤ → ℝ) (w L n : ℕ) (hp2 : p 2 = n) :
    ∃ k, k ≤ 35 * n * n + 5 * n + 19 ∧
      ((step R)^[k] ⟨⟨o, r, p, M⟩, false, w, L⟩).halted = true ∧
      outputOf ((step R)^[k] ⟨⟨o, r, p, M⟩, false, w, L⟩) =
        [if M (-3) + M (-5) - ∑ t ∈ Finset.range n, ∑ i ∈ Finset.range n,
          fval M (-2) (-7) (-7 - ((n : ℤ) + n)) t i ≤ 0 then 0 else 1] := by
  have f0 : R[o]? = some (.core (.const 0 0)) := by rw [← Nat.add_zero o, hF 0 (by norm_num)]; rfl
  have f1 : R[o + 1]? = some (.core (.pset 27 (-2))) := by rw [hF 1 (by norm_num)]; rfl
  have f2 : R[o + 2]? = some (.core (.pset 30 (-7))) := by rw [hF 2 (by norm_num)]; rfl
  have f3 : R[o + 3]? = some (.padd 36 2 2) := by rw [hF 3 (by norm_num)]; rfl
  have f4 : R[o + 4]? = some (.psub 33 30 36) := by rw [hF 4 (by norm_num)]; rfl
  have f5 : R[o + 5]? = some (.core (.pset 3 0)) := by rw [hF 5 (by norm_num)]; rfl
  have hpre : ∃ r1 p1, (step R)^[6] (⟨⟨o, r, p, M⟩, false, w, L⟩ : State) = ⟨⟨o + 6, r1, p1, M⟩, false, w + 6, L⟩ ∧ r1 0 = 0 ∧ p1 2 = n ∧ p1 3 = 0 ∧ p1 27 = -2 ∧ p1 30 = -7 ∧ p1 33 = -7 - ((n : ℤ) + n) := by
    rw [show (step R)^[6] (⟨⟨o, r, p, M⟩, false, w, L⟩ : State) = step R (step R (step R (step R (step R (step R (⟨⟨o, r, p, M⟩, false, w, L⟩ : State)))))) from rfl]
    rw [xs_core R _ _ _ _ _ _ _ f0]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
    rw [xs_core R _ _ _ _ _ _ _ f1]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
    rw [xs_core R _ _ _ _ _ _ _ f2]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
    rw [xs_padd R _ _ _ _ _ _ _ _ _ f3]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
    rw [xs_psub R _ _ _ _ _ _ _ _ _ f4]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
    rw [xs_core R _ _ _ _ _ _ _ f5]
    simp only [coreExec, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, Nat.reduceEqDiff, reduceIte, le_refl]
    refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hp2]
  obtain ⟨r1, p1, he1, g0, g2, g3, g27, g30, g33⟩ := hpre
  obtain ⟨k2, r2, p2, hk2, he2, h0, gF, gr⟩ := segF_outer R o hF M L n n r1 p1 (w + 6) g2
    (by rw [g2, g3]; simp)
  obtain ⟨h1, h2⟩ := segF_end R o hF r2 p2 M (w + 6 + k2) L
  refine ⟨12 + k2 + 6, ?_, ?_, ?_⟩
  · have : (35 * n + 5) * n + 1 = 35 * n * n + 5 * n + 1 := by ring
    omega
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, he1, he2, h1]
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, he1, he2, h2, h0, g0, g27, g30,
      g33, g3]
    simp


def blk (b c base cont sp : ℕ) (Q : Program) : List Instr :=
  Q.flatMap fun ins => [(tr b c base cont sp ins).1, (tr b c base cont sp ins).2.1,
    (tr b c base cont sp ins).2.2]

lemma blk_length (b c base cont sp : ℕ) (Q : Program) :
    (blk b c base cont sp Q).length = 3 * Q.length := by
  induction Q with
  | nil => rfl
  | cons a Q ih => simp only [blk, List.flatMap_cons, List.length_append] at ih ⊢; rw [ih]; simp; try ring

lemma blk_get (b c base cont sp : ℕ) : ∀ (Q : Program) (i : ℕ) (ins : Instr), Q[i]? = some ins →
    (blk b c base cont sp Q)[3 * i]? = some (tr b c base cont sp ins).1 ∧
    (blk b c base cont sp Q)[3 * i + 1]? = some (tr b c base cont sp ins).2.1 ∧
    (blk b c base cont sp Q)[3 * i + 2]? = some (tr b c base cont sp ins).2.2 := by
  intro Q
  induction Q with
  | nil => intro i ins h; simp at h
  | cons a Q ih =>
    intro i ins h
    have hb : blk b c base cont sp (a :: Q) = [(tr b c base cont sp a).1, (tr b c base cont sp a).2.1,
        (tr b c base cont sp a).2.2] ++ blk b c base cont sp Q := by simp [blk]
    rw [hb]
    cases i with
    | zero => simp at h; subst h; simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨h1, h2, h3⟩ := ih i ins h
      refine ⟨?_, ?_, ?_⟩
      · rw [List.getElem?_append_right (by simp <;> omega)]; simp only [List.length_cons,
          List.length_nil]; rw [show 3 * (i + 1) - (0 + 1 + 1 + 1) = 3 * i by omega]; exact h1
      · rw [List.getElem?_append_right (by simp <;> omega)]; simp only [List.length_cons,
          List.length_nil]; rw [show 3 * (i + 1) + 1 - (0 + 1 + 1 + 1) = 3 * i + 1 by omega]; exact h2
      · rw [List.getElem?_append_right (by simp <;> omega)]; simp only [List.length_cons,
          List.length_nil]; rw [show 3 * (i + 1) + 2 - (0 + 1 + 1 + 1) = 3 * i + 2 by omega]; exact h3

def oC (Q : Program) : ℕ := 12 + 3 * Q.length
def oE (Q : Program) : ℕ := oC Q + 37
def oF (Q P : Program) : ℕ := oE Q + 3 * P.length

def RP (Q P : Program) : Program :=
  segA ++ (blk 1 1 12 (oC Q) 12 Q ++ (segD (oC Q) ++ (blk 2 0 (oE Q) (oF Q P) 12 P ++
    segF (oF Q P))))

lemma get_app_right {α : Type} (l1 l2 : List α) (k : ℕ) : (l1 ++ l2)[l1.length + k]? = l2[k]? := by
  rw [List.getElem?_append_right (by omega)]; congr 1; omega

lemma segA_length : segA.length = 12 := rfl
lemma segD_length (o : ℕ) : (segD o).length = 37 := rfl
lemma segF_length (o : ℕ) : (segF o).length = 60 := rfl

lemma RP_A (Q P : Program) : ∀ k < 12, (RP Q P)[k]? = segA[k]? := by
  intro k hk
  rw [RP, List.getElem?_append_left (by rw [segA_length]; exact hk)]

lemma RP_D (Q P : Program) : ∀ k < 37, (RP Q P)[oC Q + k]? = (segD (oC Q))[k]? := by
  intro k hk
  have : oC Q + k = segA.length + ((blk 1 1 12 (oC Q) 12 Q).length + k) := by
    rw [segA_length, blk_length, oC]; ring
  rw [this, RP, get_app_right, get_app_right, List.getElem?_append_left (by rw [segD_length]; exact hk)]

lemma RP_F (Q P : Program) : ∀ k < 60, (RP Q P)[oF Q P + k]? = (segF (oF Q P))[k]? := by
  intro k hk
  have : oF Q P + k = segA.length + ((blk 1 1 12 (oC Q) 12 Q).length + ((segD (oC Q)).length +
      ((blk 2 0 (oE Q) (oF Q P) 12 P).length + k))) := by
    rw [segA_length, blk_length, blk_length, segD_length, oF, oE, oC]; ring
  rw [this, RP, get_app_right, get_app_right, get_app_right, get_app_right]

lemma RP_embQ (Q P : Program) : Embeds (RP Q P) Q 1 1 12 (oC Q) 12 := by
  intro i ins h
  have hi : i < Q.length := by
    rcases (List.getElem?_eq_some_iff.mp h) with ⟨hi, _⟩; exact hi
  obtain ⟨h1, h2, h3⟩ := blk_get 1 1 12 (oC Q) 12 Q i ins h
  have hl := blk_length 1 1 12 (oC Q) 12 Q
  have e : ∀ r < 3, (RP Q P)[12 + 3 * i + r]? = (blk 1 1 12 (oC Q) 12 Q)[3 * i + r]? := by
    intro r hr
    rw [RP, show 12 + 3 * i + r = segA.length + (3 * i + r) by rw [segA_length]; ring, get_app_right,
      List.getElem?_append_left (by rw [hl]; omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [show 12 + 3 * i = 12 + 3 * i + 0 by ring, e 0 (by norm_num)]; exact h1
  · rw [e 1 (by norm_num)]; exact h2
  · rw [e 2 (by norm_num)]; exact h3

lemma RP_embP (Q P : Program) : Embeds (RP Q P) P 2 0 (oE Q) (oF Q P) 12 := by
  intro i ins h
  have hi : i < P.length := by
    rcases (List.getElem?_eq_some_iff.mp h) with ⟨hi, _⟩; exact hi
  obtain ⟨h1, h2, h3⟩ := blk_get 2 0 (oE Q) (oF Q P) 12 P i ins h
  have hl := blk_length 2 0 (oE Q) (oF Q P) 12 P
  have e : ∀ r < 3, (RP Q P)[oE Q + 3 * i + r]? = (blk 2 0 (oE Q) (oF Q P) 12 P)[3 * i + r]? := by
    intro r hr
    have : oE Q + 3 * i + r = segA.length + ((blk 1 1 12 (oC Q) 12 Q).length +
      ((segD (oC Q)).length + (3 * i + r))) := by
      rw [segA_length, blk_length, segD_length, oE, oC]; ring
    rw [RP, this, get_app_right, get_app_right, get_app_right,
      List.getElem?_append_left (by rw [hl]; omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [show oE Q + 3 * i = oE Q + 3 * i + 0 by ring, e 0 (by norm_num)]; exact h1
  · rw [e 1 (by norm_num)]; exact h2
  · rw [e 2 (by norm_num)]; exact h3

lemma adm_cons (op : Instr) (l : List Instr) (h1 : Admissible [op]) (h2 : Admissible l) :
    Admissible (op :: l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact h1 x (by simp)
  · exact h2 x hx

lemma adm_append (l1 l2 : List Instr) (h1 : Admissible l1) (h2 : Admissible l2) :
    Admissible (l1 ++ l2) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h1 x hx
  · exact h2 x hx

lemma adm_nil : Admissible [] := by intro x hx; simp at hx

lemma adm_const (d : ℕ) (n : ℕ) : Admissible [.core (.const d (n : ℝ))] := by
  intro x hx; simp at hx; subst hx; exact ⟨n, by simp⟩

lemma adm_one (op : Instr) (h : ∀ d v, op ≠ .core (.const d v)) (ha : op ≠ .core .accept)
    (hr : op ≠ .core .reject) : Admissible [op] := by
  intro x hx; simp at hx; subst hx
  rcases x with i | _ | _ | _ | _ | _
  · rcases i with ⟨d, v⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    · exact absurd rfl (h d v)
    all_goals first | trivial | exact absurd rfl ha | exact absurd rfl hr
  all_goals trivial

lemma tr_adm (b c base cont sp : ℕ) (ins : Instr) (h : Admissible [ins]) :
    Admissible [(tr b c base cont sp ins).1, (tr b c base cont sp ins).2.1,
      (tr b c base cont sp ins).2.2] := by
  rcases ins with i | _ | _ | _ | _ | _
  · rcases i with ⟨d, v⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    · obtain ⟨q, hq⟩ : ∃ q : ℚ, v = q := h (.core (.const d v)) (by simp)
      intro x hx; simp [tr, nop] at hx
      rcases hx with rfl | rfl
      · trivial
      · exact ⟨q, hq⟩
    all_goals
      intro x hx; simp [tr, nop] at hx
      first
        | (rcases hx with rfl | rfl | rfl <;> trivial)
        | (rcases hx with rfl | rfl <;> trivial)
        | (subst hx; trivial)
        | (rcases hx with rfl | rfl | rfl <;> (try split_ifs) <;> trivial)
  all_goals
    intro x hx; simp [tr, nop] at hx
    first
      | (rcases hx with rfl | rfl | rfl <;> trivial)
      | (rcases hx with rfl | rfl <;> trivial)
      | (subst hx; trivial)

lemma blk_adm (b c base cont sp : ℕ) (Q : Program) (hQ : Admissible Q) :
    Admissible (blk b c base cont sp Q) := by
  intro x hx
  simp only [blk, List.mem_flatMap] at hx
  obtain ⟨ins, hins, hx⟩ := hx
  exact tr_adm b c base cont sp ins (fun y hy => by simp at hy; subst hy; exact hQ _ hins) x hx


lemma RP_adm (Q P : Program) (hQ : Admissible Q) (hP : Admissible P) : Admissible (RP Q P) := by
  have hA : Admissible segA := by simp [Admissible, segA]
  have hD : ∀ o, Admissible (segD o) := fun o => by
    simp [Admissible, segD]; exact ⟨⟨1, by simp⟩, ⟨2, by norm_num⟩, ⟨0, by simp⟩⟩
  have hF : ∀ o, Admissible (segF o) := fun o => by
    simp [Admissible, segF]; exact ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ⟨0, by simp⟩⟩
  unfold RP
  exact adm_append _ _ hA (adm_append _ _ (blk_adm _ _ _ _ _ _ hQ) (adm_append _ _ (hD _)
    (adm_append _ _ (blk_adm _ _ _ _ _ _ hP) (hF _))))

lemma state_eta (t : State) (q : ℕ) (hpc : t.core.pc = q) (hh : t.halted = false) :
    t = ⟨⟨q, t.core.regs, t.core.ptrs, t.core.mem⟩, false, t.work, t.inputLength⟩ := by
  obtain ⟨⟨pc, r, p, m⟩, h, w, l⟩ := t
  simp only at hpc hh
  subst hpc hh; rfl

lemma iter_work (R : Program) : ∀ (j : ℕ) (t : State), ((step R)^[j] t).halted = false →
    ((step R)^[j] t).work = t.work + j := by
  intro j
  induction j with
  | zero => intro t _; rfl
  | succ j ih =>
    intro t h
    rw [Function.iterate_succ_apply'] at h ⊢
    have h' : ((step R)^[j] t).halted = false := by
      cases hh : ((step R)^[j] t).halted
      · rfl
      · rw [step_halted R _ hh, hh] at h; exact absurd h (by simp)
    rw [(step_work_len R _ h').1, ih t h']; ring

lemma outputOf_spec (s : State) (l : List ℝ) (h : outputOf s = l) :
    (s.core.ptrs 0).toNat = l.length ∧
      ∀ i : ℕ, i < l.length → s.core.mem (-((i : ℤ) + 1)) = l.getD i 0 := by
  subst h
  refine ⟨by simp [outputOf], fun i hi => ?_⟩
  simp only [outputOf, List.length_ofFn] at hi
  simp [outputOf, List.getD_eq_getElem?_getD, hi]

lemma init_good (xs : List ℝ) (b c : ℕ) (hb : b < 3) (hb0 : b ≠ 0) (t : State)
    (hr : ∀ k, k % 3 = b → t.core.regs k = 0) (hp : ∀ k, k % 3 = b → t.core.ptrs k = 0)
    (hm : ∀ z, t.core.mem (2 * z + c) = (initState xs).core.mem z)
    (hh : t.halted = false) (sp : ℕ) :
    Good b c sp t t (initState xs) ∧ TimeOK t t (initState xs) := by
  refine ⟨⟨hh, rfl, ⟨fun i => ?_, fun i => ?_, hm, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => rfl⟩⟩, ?_⟩
  · rw [hr _ (by omega)]; rfl
  · rw [hp _ (by omega)]; rfl
  · unfold TimeOK; omega

lemma RP_no (Q P : Program) (xs : List ℝ) (kQ : ℕ) (hk : (run Q xs kQ).halted = true)
    (ho : outputOf (run Q xs kQ) = [0]) :
    ∃ k, k ≤ 8 * xs.length + 13 + 3 * (kQ + xs.length) + 3 + 7 ∧
      (run (RP Q P) xs k).halted = true ∧ outputOf (run (RP Q P) xs k) = [0] := by
  set R := RP Q P
  obtain ⟨rA, pA, mA, heA, hrA, hpA, hm1, hm0⟩ := segA_spec R (RP_A Q P) xs
  set tA : State := ⟨⟨12, rA, pA, mA⟩, false, 8 * xs.length + 13, xs.length⟩ with htA
  obtain ⟨hG, hT⟩ := init_good xs 1 1 (by norm_num) (by norm_num) tA
    (fun k hk => hrA k (by omega)) (fun k hk => hpA k (by omega)) (fun z => hm1 z) rfl 12
  obtain ⟨jB, hGB, hpcB, htmB⟩ := sim_run Q R 1 1 12 (oC Q) 12 (by norm_num) (by norm_num)
    (Or.inr rfl) (RP_embQ Q P) tA kQ (initState xs) tA hG (by simp [tA, initState]) rfl hT hk
  set tB := (step R)^[jB] tA with htB
  have hwB := iter_work R jB tA hGB.1
  have hmB : tB.core.mem (-1) = 0 := by
    have h1 := hGB.2.2.mem (-1)
    have h2 := (outputOf_spec _ _ ho).2 0 (by simp)
    simp only [Nat.cast_one] at h1
    norm_num at h1 h2
    rw [h1]; exact h2
  have hpre : run R xs (jB + (8 * xs.length + 13)) = tB := by
    rw [run, Function.iterate_add_apply, heA]
  rw [state_eta tB (oC Q) hpcB hGB.1] at hpre
  obtain ⟨hh, hout⟩ := segD_no R (oC Q) (RP_D Q P) tB.core.regs tB.core.ptrs tB.core.mem
    tB.work tB.inputLength (by rw [hmB])
  refine ⟨7 + (jB + (8 * xs.length + 13)), ?_, ?_, ?_⟩
  · have e1 : tA.work = 8 * xs.length + 13 := rfl
    have e2 : tA.inputLength = xs.length := rfl
    have e3 : (initState xs).work = 0 := rfl
    have e4 : (initState xs).inputLength = xs.length := rfl
    have e5 : tB.inputLength = tA.inputLength := hGB.2.1
    rw [← htB] at hwB
    omega
  · rw [run, Function.iterate_add_apply, ← run, hpre]; exact hh
  · rw [run, Function.iterate_add_apply, ← run, hpre]; exact hout


lemma fval_sum {n m : ℕ} (M : ℤ → ℝ) (p w : Fin n → ℝ) (σ : Fin n → Fin m)
    (hσ : ∀ j : Fin n, M (-2 - ((j : ℤ) + j)) = ((σ j : ℕ) : ℝ))
    (hp : ∀ j : Fin n, M (-7 - ((j : ℤ) + j)) = p j)
    (hw : ∀ j : Fin n, M (-7 - ((n : ℤ) + n) - ((j : ℤ) + j)) = w j) :
    ∑ t ∈ Finset.range n, ∑ i ∈ Finset.range n, fval M (-2) (-7) (-7 - ((n : ℤ) + n)) t i =
      smithCost p w σ := by
  rw [Finset.sum_range]
  unfold smithCost
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_range]
  unfold smithCompletion
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 : ((t : ℕ) : ℤ) = ((t : ℕ) : ℤ) := rfl
  unfold fval
  rw [hσ t, hσ i, hp t, hp i, hw t, hw i]
  have hc : (((σ t : ℕ) : ℝ) = ((σ i : ℕ) : ℝ)) ↔ σ i = σ t := by
    rw [Nat.cast_inj, eq_comm, Fin.val_inj]
  have hl : (((i : ℕ) : ℤ) ≤ ((t : ℕ) : ℤ)) ↔ i ≤ t := by
    rw [Nat.cast_le, Fin.val_fin_le]
  simp only [hc, hl]

lemma layout (n : ℕ) (ε : ℝ) (p w : Fin n → ℝ) (mB : ℤ → ℝ) (h0 : ∀ z, mB (2 * z) = 0)
    (v : ℤ → ℝ) (hv : ∀ t, v t = (List.ofFn p ++ List.ofFn w).getD t.toNat 0) (z : ℤ) :
    memD (fun y => if y = 2 then ε else if y = 0 then (2 * n + 1 : ℝ) else mB y) v
      ((2 * n : ℕ) : ℤ) (2 * z + ((0 : ℕ) : ℤ)) = (initState (schedInput ε p w)).core.mem z := by
  simp only [memD, initState, schedInput, Nat.cast_zero, add_zero]
  have hlen : (ε :: (List.ofFn p ++ List.ofFn w)).length = 2 * n + 1 := by simp; ring
  by_cases hz0 : z = 0
  · subst hz0; simp [hlen]
  by_cases hz1 : z = 1
  · subst hz1; simp
  by_cases hneg : z < 0
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), h0, if_neg hz0, if_neg (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = k := ⟨z.toNat, by omega⟩
  rw [if_neg hz0, if_pos (show (0 : ℤ) < k by omega)]
  have hk : 2 ≤ k := by omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [show ((j + 2 : ℕ) : ℤ).toNat - 1 = j + 1 by omega, List.cons_append, List.getD_cons_succ]
  by_cases hj : j < 2 * n
  · rw [if_pos (by push_cast; omega), hv]
    congr 1; omega
  · rw [if_neg (by push_cast; omega), if_neg (by omega), if_neg (by omega), h0]
    rw [List.getD_eq_default]
    simp; omega


lemma getD_pw {n : ℕ} (p w : Fin n → ℝ) (j : Fin n) :
    (List.ofFn p ++ List.ofFn w).getD (j : ℕ) 0 = p j ∧
    (List.ofFn p ++ List.ofFn w).getD (n + (j : ℕ)) 0 = w j := by
  constructor
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

lemma natOutput_eq (l : List ℕ) : natOutput l = List.map (Nat.cast : ℕ → ℝ) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [natOutput] at ih ⊢
    simp at ih ⊢
    exact ih

lemma assign_len {n m : ℕ} (σ : Fin n → Fin m) : (assignmentOutput σ).length = n := by
  unfold assignmentOutput; rw [natOutput_eq]; simp

lemma assign_get {n m : ℕ} (σ : Fin n → Fin m) (j : Fin n) :
    (assignmentOutput σ).getD j 0 = ((σ j : ℕ) : ℝ) := by
  unfold assignmentOutput; rw [natOutput_eq, List.getD_eq_getElem?_getD]; simp

lemma RP_yes (Q P : Program) (xs : List ℝ) (kQ : ℕ) (hk : (run Q xs kQ).halted = true)
    (n : ℕ) (hn : 1 ≤ n) (G : GapData n) (ho : outputOf (run Q xs kQ) = gapOutput G) {m : ℕ}
    (σ : Fin n → Fin m) (kP : ℕ)
    (hkP : (run P (schedInput (epsOf G.upper G.gap) G.p G.w) kP).halted = true)
    (hoP : outputOf (run P (schedInput (epsOf G.upper G.gap) G.p G.w) kP) =
      assignmentOutput σ) :
    ∃ k, k ≤ 8 * xs.length + 13 + (3 * (kQ + xs.length) + 3) + (16 * n + 26) +
        (3 * (kP + (2 * n + 1)) + 3) + (35 * n * n + 5 * n + 19) ∧
      (run (RP Q P) xs k).halted = true ∧
      outputOf (run (RP Q P) xs k) =
        [if G.upper + G.gap - smithCost G.p G.w σ ≤ 0 then 0 else 1] := by
  set R := RP Q P
  obtain ⟨rA, pA, mA, heA, hrA, hpA, hm1, hm0⟩ := segA_spec R (RP_A Q P) xs
  set tA : State := ⟨⟨12, rA, pA, mA⟩, false, 8 * xs.length + 13, xs.length⟩ with htA
  obtain ⟨hG, hT⟩ := init_good xs 1 1 (by norm_num) (by norm_num) tA
    (fun k hk => hrA k (by omega)) (fun k hk => hpA k (by omega)) (fun z => hm1 z) rfl 12
  obtain ⟨jB, hGB, hpcB, htmB⟩ := sim_run Q R 1 1 12 (oC Q) 12 (by norm_num) (by norm_num)
    (Or.inr rfl) (RP_embQ Q P) tA kQ (initState xs) tA hG (by simp [tA, initState]) rfl hT hk
  set tB := (step R)^[jB] tA with htB
  have hwB := iter_work R jB tA hGB.1
  rw [← htB] at hwB
  obtain ⟨hlenQ, hvalQ⟩ := outputOf_spec _ _ ho
  unfold run at hlenQ hvalQ
  have hglen : (gapOutput G).length = 2 * n + 3 := by simp [gapOutput]; ring
  have hQm : ∀ u : ℕ, u < 2 * n + 3 →
      tB.core.mem (-2 * (u : ℤ) - 1) = (gapOutput G).getD u 0 := by
    intro u hu
    have h1 := hGB.2.2.mem (-((u : ℤ) + 1))
    rw [← hvalQ u (by rw [hglen]; exact hu), ← h1]
    congr 1; push_cast; ring
  have hmB1 : tB.core.mem (-1) = 1 := by
    have := hQm 0 (by omega); simpa [gapOutput] using this
  have hmB3 : tB.core.mem (-3) = G.upper := by
    have := hQm 1 (by omega); norm_num [gapOutput] at this; exact this
  have hmB5 : tB.core.mem (-5) = G.gap := by
    have := hQm 2 (by omega); norm_num [gapOutput] at this; exact this
  have hpB1 : tB.core.ptrs 1 = 2 * (n : ℤ) + 3 := by
    have h1 := hGB.2.2.ptrs 0
    simp only [Nat.mul_zero, Nat.zero_add] at h1
    rw [h1]; rw [hglen] at hlenQ; omega
  set v : ℤ → ℝ := fun t => (List.ofFn G.p ++ List.ofFn G.w).getD t.toNat 0 with hvdef
  have hv : ∀ t : ℕ, t < 2 * n → tB.core.mem (-7 - 2 * (t : ℤ)) = v t := by
    intro t ht
    have := hQm (t + 3) (by omega)
    rw [show -2 * ((t + 3 : ℕ) : ℤ) - 1 = -7 - 2 * (t : ℤ) by push_cast; ring] at this
    rw [this]
    simp only [v, gapOutput, Int.toNat_natCast]
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp)]
    simp
  have hpre : run R xs (jB + (8 * xs.length + 13)) = tB := by
    rw [run, Function.iterate_add_apply, heA]
  rw [state_eta tB (oC Q) hpcB hGB.1] at hpre
  obtain ⟨jD, rD, pD, mD, hjD, heD, hrD, hpD, hmD⟩ := segD_yes R (oC Q) (RP_D Q P)
    tB.core.regs tB.core.ptrs tB.core.mem tB.work tB.inputLength (by rw [hmB1]; norm_num) n
    hpB1 v hv
  rw [hmB3, hmB5] at hmD
  set ε := epsOf G.upper G.gap with hε
  set tD : State := ⟨⟨oC Q + 37, rD, pD, mD⟩, false, tB.work + jD, tB.inputLength⟩ with htD
  set xsP := schedInput ε G.p G.w with hxsP
  have hzero_even : ∀ z, tB.core.mem (2 * z) = 0 := fun z => by
    rw [hGB.2.2.fmem (2 * z) (by omega)]; exact hm0 z
  obtain ⟨hG2, hT2⟩ := init_good xsP 2 0 (by norm_num) (by norm_num) tD
    (fun k hk => by
      show rD k = 0
      rw [hrD k (by omega), hGB.2.2.fregs k (by omega)]; exact hrA k (by omega))
    (fun k hk => by
      show pD k = 0
      rw [hpD k (by omega), hGB.2.2.fptrs k (by omega) (by omega)]; exact hpA k (by omega))
    (fun z => by
      show mD _ = _
      rw [hmD]; exact layout n ε G.p G.w tB.core.mem hzero_even v (fun t => rfl) z) rfl 12
  obtain ⟨jE, hGE, hpcE, htmE⟩ := sim_run P R 2 0 (oE Q) (oF Q P) 12 (by norm_num)
    (by norm_num) (Or.inl rfl) (RP_embP Q P) tD kP (initState xsP) tD hG2
    (by simp [tD, initState, oE]) rfl hT2 hkP
  set tE := (step R)^[jE] tD with htE
  have hwE := iter_work R jE tD hGE.1
  rw [← htE] at hwE
  obtain ⟨hlenP, hvalP⟩ := outputOf_spec _ _ hoP
  unfold run at hlenP hvalP
  have halen : (assignmentOutput σ).length = n := assign_len σ
  have hpE2 : tE.core.ptrs 2 = n := by
    have h1 := hGE.2.2.ptrs 0
    simp only [Nat.mul_zero, Nat.zero_add] at h1
    rw [h1]; rw [halen] at hlenP
    omega
  have hodd : ∀ y : ℤ, y % 2 = 1 → tE.core.mem y = tB.core.mem y := by
    intro y hy
    rw [hGE.2.2.fmem y (by omega)]
    show mD y = _
    rw [hmD]; simp only [memD]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hσ : ∀ j : Fin n, tE.core.mem (-2 - ((j : ℤ) + j)) = ((σ j : ℕ) : ℝ) := by
    intro j
    have h1 := hGE.2.2.mem (-((j : ℤ) + 1))
    have h2 := hvalP j (by rw [halen]; exact j.2)
    rw [show -2 - ((j : ℤ) + j) = 2 * (-((j : ℤ) + 1)) + ((0 : ℕ) : ℤ) by push_cast; ring, h1, h2]
    exact assign_get σ j
  have hp : ∀ j : Fin n, tE.core.mem (-7 - ((j : ℤ) + j)) = G.p j := by
    intro j
    rw [hodd _ (by omega), show -7 - ((j : ℤ) + j) = -7 - 2 * ((j : ℕ) : ℤ) by ring,
      hv j (by omega)]
    simp only [v, Int.toNat_natCast]
    exact (getD_pw G.p G.w j).1
  have hw : ∀ j : Fin n, tE.core.mem (-7 - ((n : ℤ) + n) - ((j : ℤ) + j)) = G.w j := by
    intro j
    rw [hodd _ (by omega), show -7 - ((n : ℤ) + n) - ((j : ℤ) + j) = -7 - 2 * ((n + j : ℕ) : ℤ)
      by push_cast; ring, hv (n + j) (by omega)]
    simp only [v, Int.toNat_natCast]
    exact (getD_pw G.p G.w j).2
  obtain ⟨kF, hkF, hhF, hoF⟩ := segF_spec R (oF Q P) (RP_F Q P) tE.core.regs tE.core.ptrs
    tE.core.mem tE.work tE.inputLength n hpE2
  rw [hodd (-3) (by norm_num), hodd (-5) (by norm_num), hmB3, hmB5,
    fval_sum _ _ _ σ hσ hp hw] at hoF
  have hrun : run R xs (kF + (jE + (jD + (jB + (8 * xs.length + 13))))) =
      (step R)^[kF] ⟨⟨oF Q P, tE.core.regs, tE.core.ptrs, tE.core.mem⟩, false, tE.work,
        tE.inputLength⟩ := by
    rw [run, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
      ← run, hpre, heD, ← state_eta tE (oF Q P) hpcE hGE.1]
  refine ⟨kF + (jE + (jD + (jB + (8 * xs.length + 13)))), ?_, by rw [hrun]; exact hhF,
    by rw [hrun]; exact hoF⟩
  have e1 : tA.work = 8 * xs.length + 13 := rfl
  have e2 : tA.inputLength = xs.length := rfl
  have e3 : (initState xs).work = 0 := rfl
  have e4 : (initState xs).inputLength = xs.length := rfl
  have e5 : tB.inputLength = tA.inputLength := hGB.2.1
  have e6 : (initState xsP).work = 0 := rfl
  have e7 : (initState xsP).inputLength = 2 * n + 1 := by
    show xsP.length = _; simp [xsP, schedInput]; ring
  have e8 : tE.inputLength = tD.inputLength := hGE.2.1
  have e9 : tD.work = tB.work + jD := rfl
  have e10 : tD.inputLength = tB.inputLength := rfl
  omega


lemma smith_key_le {n : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (i j : Fin n) :
    toLex (-(w i / p i), (i : ℕ)) ≤ toLex (-(w j / p j), (j : ℕ)) ↔ SmithBefore p w i j := by
  rw [Prod.Lex.le_iff]
  simp only [SmithBefore, ofLex_toLex]
  have hi := hp i
  have hj := hp j
  have e1 : -(w i / p i) < -(w j / p j) ↔ w j * p i < w i * p j := by
    rw [neg_lt_neg_iff, div_lt_div_iff₀ hj hi]
  have e2 : -(w i / p i) = -(w j / p j) ↔ w j * p i = w i * p j := by
    rw [neg_inj, div_eq_div_iff hi.ne' hj.ne']
    constructor <;> intro h <;> linarith
  rw [e1, e2, Fin.val_fin_le]

lemma exists_smith_perm {n m : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Fin n → Fin m) :
    ∃ ρ : Fin n ≃ Fin n, cost p w σ ρ = smithCost p w σ := by
  set key : Fin n → Lex (ℝ × ℕ) := fun j => toLex (-(w j / p j), (j : ℕ)) with hkey
  have hinj : Function.Injective key := by
    intro a b h
    have := congrArg (fun x => (ofLex x).2) h
    simp [key] at this
    exact Fin.ext this
  set τ := Tuple.sort key
  have hmono : Monotone (key ∘ τ) := Tuple.monotone_sort key
  have hsm : StrictMono (key ∘ τ) := hmono.strictMono_of_injective (hinj.comp τ.injective)
  refine ⟨τ.symm, ?_⟩
  unfold cost smithCost completion smithCompletion
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← smith_key_le p w hp i j]
  have : key i ≤ key j ↔ τ.symm i ≤ τ.symm j := by
    have h := hsm.le_iff_le (a := τ.symm i) (b := τ.symm j)
    simp only [Function.comp, Equiv.apply_symm_apply] at h
    exact h
  rw [this]

lemma opt_le_smithCost {n m : ℕ} (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (σ : Fin n → Fin m) :
    OPT m p w ≤ smithCost p w σ := by
  obtain ⟨ρ, hρ⟩ := exists_smith_perm p w hp σ
  rw [← hρ]
  unfold OPT
  apply csInf_le
  · have : {c : ℝ | ∃ (σ : Fin n → Fin m) (ρ : Fin n ≃ Fin n), cost p w σ ρ = c} =
        Set.range (fun x : (Fin n → Fin m) × (Fin n ≃ Fin n) => cost p w x.1 x.2) := by
      ext c; simp
    rw [this]; exact (Set.finite_range _).bddBelow
  · exact ⟨σ, ρ, rfl⟩

lemma eps_facts (Λ g : ℝ) (hΛ : 0 < Λ) (hg : 0 < g) :
    0 < epsOf Λ g ∧ epsOf Λ g ≤ 1 ∧ epsOf Λ g * Λ ≤ g / 2 ∧ 1 ≤ 1 / epsOf Λ g ∧
      1 / epsOf Λ g ≤ 1 + 2 * (Λ / g) := by
  unfold epsOf
  have h2 : 0 < Λ + Λ := by linarith
  have hq : 0 < g / (Λ + Λ) := div_pos hg h2
  split_ifs with h
  · have hle : g / (Λ + Λ) ≤ 1 := by linarith
    refine ⟨hq, hle, ?_, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, div_le_div_iff₀ h2 (by norm_num)]; nlinarith
    · rw [le_div_iff₀ hq]; linarith
    · rw [one_div_div, div_le_iff₀ hg]
      have : 0 ≤ 2 * (Λ / g) * g := by positivity
      rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hg.ne']; linarith
  · push_neg at h
    refine ⟨by norm_num, le_rfl, ?_, by norm_num, ?_⟩
    · have : 1 < g / (Λ + Λ) := by linarith
      rw [lt_div_iff₀ h2] at this; linarith
    · have : 0 ≤ Λ / g := by positivity
      norm_num; linarith

lemma itemCells_length {k : ℕ} (I : PartitionData k) : (itemCells I).length = I.n := by
  simp [itemCells, List.length_flatten, PartitionData.n, List.sum_ofFn]
  ring

lemma log_poly_bound (D : ℕ) (hD : 1 ≤ D) : ∃ K : ℝ, 0 < K ∧ ∀ N X : ℝ, 1 ≤ N → 1 ≤ X →
    (N + 1 + Real.logb 2 (X + 1)) ^ D ≤ K * N ^ D * X ^ (1 / 2 : ℝ) := by
  set δ : ℝ := 1 / (2 * D) with hδ
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hδpos : 0 < δ := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := 1 + 1 / (δ * Real.log 2) with hc
  have hcpos : 0 < c := by positivity
  refine ⟨2 ^ D * c ^ D * 2, by positivity, fun N X hN hX => ?_⟩
  have hX1 : 0 < X + 1 := by linarith
  have hlog0 : 0 ≤ Real.logb 2 (X + 1) := Real.logb_nonneg (by norm_num) (by linarith)
  have hy1 : 1 ≤ (X + 1) ^ δ := Real.one_le_rpow (by linarith) hδpos.le
  -- 1 + logb ≤ c (X+1)^δ
  have hlb : 1 + Real.logb 2 (X + 1) ≤ c * (X + 1) ^ δ := by
    have h1 : Real.log (X + 1) ≤ (X + 1) ^ δ / δ := Real.log_le_rpow_div hX1.le hδpos
    have h2 : Real.logb 2 (X + 1) ≤ (X + 1) ^ δ / (δ * Real.log 2) := by
      rw [Real.logb, div_le_div_iff₀ hl2 (by positivity)]
      calc Real.log (X + 1) * (δ * Real.log 2) = (Real.log (X + 1) * δ) * Real.log 2 := by ring
        _ ≤ (X + 1) ^ δ * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right _ hl2.le
          rw [le_div_iff₀ hδpos] at h1; linarith
    calc 1 + Real.logb 2 (X + 1) ≤ (X + 1) ^ δ + (X + 1) ^ δ / (δ * Real.log 2) := by linarith
      _ = c * (X + 1) ^ δ := by rw [hc]; field_simp
  have hsum : N + 1 + Real.logb 2 (X + 1) ≤ 2 * N * (c * (X + 1) ^ δ) := by
    have : N + 1 + Real.logb 2 (X + 1) ≤ 2 * N * (1 + Real.logb 2 (X + 1)) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left hlb (by linarith))
  have hpowD : ((X + 1) ^ δ) ^ D = (X + 1) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX1.le]
    congr 1; rw [hδ]; field_simp
  have hX2 : (X + 1) ^ (1 / 2 : ℝ) ≤ 2 * X ^ (1 / 2 : ℝ) := by
    calc (X + 1) ^ (1 / 2 : ℝ) ≤ (2 * X) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hX1.le (by linarith) (by norm_num)
      _ = 2 ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * X ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := by simp
  have h0 : 0 ≤ N + 1 + Real.logb 2 (X + 1) := by linarith
  calc (N + 1 + Real.logb 2 (X + 1)) ^ D ≤ (2 * N * (c * (X + 1) ^ δ)) ^ D :=
        pow_le_pow_left₀ h0 hsum D
    _ = 2 ^ D * c ^ D * N ^ D * ((X + 1) ^ δ) ^ D := by ring
    _ = 2 ^ D * c ^ D * N ^ D * (X + 1) ^ (1 / 2 : ℝ) := by rw [hpowD]
    _ ≤ 2 ^ D * c ^ D * N ^ D * (2 * X ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hX2 (by positivity)
    _ = 2 ^ D * c ^ D * 2 * N ^ D * X ^ (1 / 2 : ℝ) := by ring

lemma rpow_mono_one (N : ℝ) (hN : 1 ≤ N) (a b : ℝ) (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN h

lemma inv_eps_bound (u B e E : ℝ) (hu : 1 ≤ u) (huB : u ≤ B) (heE : e ≤ E) (hE : 0 ≤ E) :
    u ^ e ≤ B ^ E :=
  (Real.rpow_le_rpow_of_exponent_le hu heE).trans
    (Real.rpow_le_rpow (by linarith) huB hE)

lemma time_bound (m : ℕ) (hm : 2 ≤ m) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (CG CP : ℝ)
    (hCG : 0 < CG) (hCP : 0 < CP) (d : ℕ) :
    ∃ C' β' : ℝ, 0 < C' ∧ 0 < β' ∧ ∀ (n W : ℕ) (Λ g : ℝ) (kQ kP : ℕ), 1 ≤ n → 1 ≤ W →
      0 < Λ → 0 < g → Λ / g ≤ CG * (n : ℝ) ^ d * (W : ℝ) ^ 2 →
      (kQ : ℝ) ≤ CG * ((n : ℝ) + 1 + Real.logb 2 ((W : ℝ) + 1)) ^ d →
      (kP : ℝ) ≤ CP * (n : ℝ) ^ β * (1 / epsOf Λ g) ^ (((m : ℝ) - 1) / 2 - α) →
      ((3 * kQ + 3 * kP + 200 * n * n : ℕ) : ℝ) ≤
        C' * (n : ℝ) ^ β' * (W : ℝ) ^ ((m : ℝ) - 1 - min α (1 / 2)) := by
  set η := min α (1 / 2) with hηdef
  set γ : ℝ := (m : ℝ) - 1 - η with hγdef
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  have hηα : η ≤ α := min_le_left _ _
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hγ : 1 / 2 ≤ γ := by rw [hγdef]; linarith
  set e : ℝ := ((m : ℝ) - 1) / 2 - α with hedef
  set E : ℝ := max e 0 with hEdef
  have hE0 : 0 ≤ E := le_max_right _ _
  have heE : e ≤ E := le_max_left _ _
  have h2E : 2 * E ≤ γ := by
    rcases le_total e 0 with h | h
    · rw [hEdef, max_eq_right h]; linarith
    · rw [hEdef, max_eq_left h, hedef, hγdef]; linarith
  obtain ⟨K, hK, hlog⟩ := log_poly_bound (d + 1) (by omega)
  set B0 : ℝ := 1 + 2 * CG with hB0
  have hB0pos : 0 < B0 := by rw [hB0]; linarith
  set β' : ℝ := β + d * E + (d + 1) + 2 with hβ'
  have hdE : 0 ≤ (d : ℝ) * E := mul_nonneg (Nat.cast_nonneg _) hE0
  refine ⟨3 * CG * K + 3 * CP * B0 ^ E + 200, β', by positivity, by rw [hβ']; positivity, ?_⟩
  intro n W Λ g kQ kP hn hW hΛ hg hratio hkQ hkP
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set N : ℝ := (n : ℝ) with hNdef
  set X : ℝ := (W : ℝ) with hXdef
  have hXγ : 1 ≤ X ^ γ := Real.one_le_rpow hX (by linarith)
  have hNβ' : 1 ≤ N ^ β' := Real.one_le_rpow hN (by rw [hβ']; positivity)
  have hXγ0 : 0 ≤ X ^ γ := by positivity
  have hNβ'0 : 0 ≤ N ^ β' := by positivity
  -- the Q term
  have tQ : (kQ : ℝ) ≤ CG * K * N ^ β' * X ^ γ := by
    have hb1 : 1 ≤ N + 1 + Real.logb 2 (X + 1) := by
      have := Real.logb_nonneg (b := 2) (by norm_num) (by linarith : (1 : ℝ) ≤ X + 1)
      linarith
    have s1 : (N + 1 + Real.logb 2 (X + 1)) ^ d ≤ (N + 1 + Real.logb 2 (X + 1)) ^ (d + 1) :=
      pow_le_pow_right₀ hb1 (by omega)
    have s2 := hlog N X hN hX
    have s3 : N ^ (d + 1) ≤ N ^ β' := by
      rw [← Real.rpow_natCast]
      apply rpow_mono_one N hN; push_cast; rw [hβ']; linarith
    have s4 : X ^ (1 / 2 : ℝ) ≤ X ^ γ := rpow_mono_one X hX _ _ hγ
    calc (kQ : ℝ) ≤ CG * (N + 1 + Real.logb 2 (X + 1)) ^ d := hkQ
      _ ≤ CG * (K * N ^ (d + 1) * X ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (s1.trans s2) hCG.le
      _ ≤ CG * (K * N ^ β' * X ^ γ) := by
          apply mul_le_mul_of_nonneg_left _ hCG.le
          apply mul_le_mul (mul_le_mul_of_nonneg_left s3 hK.le) s4 (by positivity)
            (by positivity)
      _ = CG * K * N ^ β' * X ^ γ := by ring
  -- the P term
  have tP : (kP : ℝ) ≤ CP * B0 ^ E * N ^ β' * X ^ γ := by
    obtain ⟨he0, he1, heΛ, hie1, hie2⟩ := eps_facts Λ g hΛ hg
    have hNd : 1 ≤ N ^ d := one_le_pow₀ hN
    have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
    have hu : 1 / epsOf Λ g ≤ B0 * N ^ d * X ^ 2 := by
      have h1 : 1 ≤ N ^ d * X ^ 2 := one_le_mul_of_one_le_of_one_le hNd hX2
      calc 1 / epsOf Λ g ≤ 1 + 2 * (Λ / g) := hie2
        _ ≤ 1 + 2 * (CG * N ^ d * X ^ 2) := by linarith
        _ ≤ B0 * N ^ d * X ^ 2 := by rw [hB0]; nlinarith
    have hue := inv_eps_bound _ _ e E hie1 hu heE hE0
    have hsplit : (B0 * N ^ d * X ^ 2) ^ E = B0 ^ E * N ^ ((d : ℝ) * E) * X ^ (2 * E) := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hB0pos.le (by positivity),
        ← Real.rpow_natCast N d, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast X 2,
        ← Real.rpow_mul (by linarith)]
      norm_num
    have hNb : N ^ β * N ^ ((d : ℝ) * E) ≤ N ^ β' := by
      rw [← Real.rpow_add (by linarith)]
      apply rpow_mono_one N hN; rw [hβ']; linarith
    have hX2E : X ^ (2 * E) ≤ X ^ γ := rpow_mono_one X hX _ _ h2E
    calc (kP : ℝ) ≤ CP * N ^ β * (1 / epsOf Λ g) ^ e := hkP
      _ ≤ CP * N ^ β * (B0 ^ E * N ^ ((d : ℝ) * E) * X ^ (2 * E)) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left hue (by positivity)
      _ = CP * B0 ^ E * (N ^ β * N ^ ((d : ℝ) * E)) * X ^ (2 * E) := by ring
      _ ≤ CP * B0 ^ E * N ^ β' * X ^ γ := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hNb (by positivity)) hX2E (by positivity)
            (by positivity)
  -- the quadratic term
  have tn : N * N ≤ N ^ β' * X ^ γ := by
    have : N * N ≤ N ^ β' := by
      rw [show N * N = N ^ (2 : ℝ) by rw [Real.rpow_two]; ring]
      apply rpow_mono_one N hN; rw [hβ']; linarith
    nlinarith
  push_cast
  nlinarith

theorem bridge (m : ℕ) (hm : 2 ≤ m) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hG : HasGapReduction m) (hF : FastScheduling m α β) :
    ∃ β' : ℝ, 0 < β' ∧ FastGrouped m (min α (1 / 2)) β' := by
  obtain ⟨Q, CG, d, hQadm, hCG, hQ⟩ := hG
  obtain ⟨P, CP, hPadm, hCP, hP⟩ := hF
  obtain ⟨C', β', hC', hβ', hT⟩ := time_bound m hm α β hα hβ CG CP hCG hCP d
  refine ⟨β', hβ', RP Q P, C', RP_adm Q P hQadm hPadm, hC', fun I hI => ?_⟩
  obtain ⟨hs, hq, hW, _, _, _⟩ := hI
  have hn : 1 ≤ I.n := by
    unfold PartitionData.n
    have : 0 < m * I.s * I.q := Nat.mul_pos (Nat.mul_pos (by omega) hs) hq
    omega
  set xs := groupedInput I with hxs
  have hL : xs.length = I.n + 3 := by
    simp [xs, groupedInput, itemCells_length]; try ring
  obtain ⟨⟨kQ, hkQB, hkQ⟩, hbr⟩ := hQ I ⟨hs, hq, hW, ‹_›, ‹_›, ‹_›⟩
  have houtQ := output_of_halted Q xs kQ hkQ
  rcases hbr with ⟨hno, hNo⟩ | ⟨G, hoG, hGP⟩
  · rw [houtQ] at hno
    obtain ⟨k, hk, hkh, hko⟩ := RP_no Q P xs kQ hkQ (Option.some_inj.mp hno)
    have hout := output_of_halted (RP Q P) xs k hkh
    rw [hko] at hout
    refine ⟨⟨fun hy => absurd hy hNo, fun _ => hout⟩, k, ?_, hkh⟩
    have := hT I.n I.W CG 1 kQ 0 hn hW hCG (by norm_num)
      (by have : (1 : ℝ) ≤ (I.n : ℝ) ^ d * (I.W : ℝ) ^ 2 := by
            apply one_le_mul_of_one_le_of_one_le
            · exact one_le_pow₀ (by exact_mod_cast hn)
            · exact one_le_pow₀ (by exact_mod_cast hW)
          rw [div_one, mul_assoc]; nlinarith)
      (le_trans (by exact_mod_cast hkQB) le_rfl) (by
        simp only [Nat.cast_zero]
        have := (eps_facts CG 1 hCG one_pos).1
        apply mul_nonneg (mul_nonneg hCP.le (by positivity)) (Real.rpow_nonneg (by positivity) _))
    refine le_trans ?_ this
    have hk' : k ≤ 3 * kQ + 3 * 0 + 200 * I.n * I.n := by rw [hL] at hk; nlinarith
    exact_mod_cast hk'
  · rw [houtQ] at hoG
    obtain ⟨hpG, hwG, hΛ, hg, hratio, hyes, hno⟩ := hGP
    obtain ⟨he0, he1, heΛ, hie1, hie2⟩ := eps_facts G.upper G.gap hΛ hg
    obtain ⟨σ, hσo, ⟨kP, hkPB, hkP⟩, hcost⟩ := hP I.n hn G.p G.w hpG hwG _ he0 he1
    have houtP := output_of_halted P _ kP hkP
    rw [houtP] at hσo
    obtain ⟨k, hk, hkh, hko⟩ := RP_yes Q P xs kQ hkQ I.n hn G (Option.some_inj.mp hoG) σ kP
      hkP (Option.some_inj.mp hσo)
    have hout := output_of_halted (RP Q P) xs k hkh
    rw [hko] at hout
    refine ⟨⟨fun hy => ?_, fun hny => ?_⟩, k, ?_, hkh⟩
    · rw [hout]
      have h1 := hyes hy
      have hopt0 : smithCost G.p G.w σ ≤ (1 + epsOf G.upper G.gap) * G.upper :=
        hcost.trans (mul_le_mul_of_nonneg_left h1 (by linarith))
      rw [if_neg (by nlinarith)]
    · rw [hout]
      have h1 := hno hny
      have := opt_le_smithCost G.p G.w hpG σ
      rw [if_pos (by linarith)]
    · have := hT I.n I.W G.upper G.gap kQ kP hn hW hΛ hg hratio
        (le_trans (by exact_mod_cast hkQB) le_rfl) hkPB
      refine le_trans ?_ this
      have hk' : k ≤ 3 * kQ + 3 * kP + 200 * I.n * I.n := by rw [hL] at hk; nlinarith
      exact_mod_cast hk'

theorem solution_aux :
    CNFSETH → ∀ m : ℕ, 2 ≤ m → ∀ α β : ℝ, 0 < α → 0 < β →
      ¬ FastScheduling m α β := by
  intro hS m hm α β hα hβ hF
  obtain ⟨β', hβ', hFG⟩ := bridge m hm α β hα hβ (lemma_B_1 m hm) hF
  exact corollary_A_7 hS m hm (min α (1 / 2)) β' (lt_min hα (by norm_num)) hβ' hFG

end FasterWCTFPTAS.Main.Supplement

open FasterWCTFPTAS.Main.Supplement in
theorem solution :
    CNFSETH → ∀ m : ℕ, 2 ≤ m → ∀ α β : ℝ, 0 < α → 0 < β →
      ¬ FastScheduling m α β :=
  solution_aux
