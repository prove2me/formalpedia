-- Prove2me | solution 1 for CountingMatroid.Bridge.setFinsetQueryProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T16:41:50.636349+00:00
-- url     : https://prove2.me/submissions/5e355b54-0e7e-4008-80c6-105cdbf38812

import Definitions.Def_CountingMatroid_Bridge_SetFinsetQueryProgram
import Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_finset_correct

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge OAI.CommonBasesFPRAS
open scoped Classical

private theorem execution_output_some_add_steps {k s n : ℕ}
    (P : Program k s) (O : IndependenceOracle n) (c : MachineConfig k s)
    (bits : ℕ → Bool) (t d : ℕ)
    (h : (execution P O c bits t).output.isSome) :
    (execution P O c bits (t + d)).output.isSome := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
      rw [Nat.add_succ]
      simp [execution, ih, machineStep]

/-- If two programs differ only at a halt state, a run that ends before
output is written has identical configurations in both programs. -/
private theorem execution_eq_away_from_halt {k s n : ℕ}
    (P Q : Program k s) (O : IndependenceOracle n) (c : MachineConfig k s)
    (bits : ℕ → Bool) (t : ℕ) (haltState : Fin (s + 1))
    (hagree : ∀ q, q ≠ haltState → P q = Q q)
    (hhalt : P haltState = .halt)
    (hfinal : (execution P O c bits t).output = none) :
    execution P O c bits t = execution Q O c bits t := by
  have hno : ∀ m, m < t → (execution P O c bits m).control ≠ haltState := by
    intro m hmt hcontrol
    let cm := execution P O c bits m
    have hnext : (execution P O c bits (m + 1)).output.isSome := by
      have hstep : (machineStep P O (bits m) cm).output.isSome := by
        by_cases hsome : cm.output.isSome
        · simp [machineStep, hsome]
        · simp only [machineStep, hsome, ↓reduceIte]
          rw [hcontrol, hhalt]
          simp
      simpa [cm, execution] using hstep
    have htail := execution_output_some_add_steps P O c bits (m + 1)
      (t - (m + 1)) hnext
    have hindex : m + 1 + (t - (m + 1)) = t := by omega
    rw [hindex, hfinal] at htail
    simpa using htail
  have hrun : ∀ m, m ≤ t → execution P O c bits m = execution Q O c bits m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
        intro hmt
        have hprev := ih (by omega)
        have hcontrol := hno m (by omega)
        simp only [execution]
        rw [hprev]
        have hcontrolQ : (execution Q O c bits m).control ≠ haltState := by
          simpa [hprev] using hcontrol
        have hprogram := hagree _ hcontrolQ
        change machineStep P O (bits m) (execution Q O c bits m) =
          machineStep Q O (bits m) (execution Q O c bits m)
        by_cases hsome : (execution Q O c bits m).output.isSome <;>
          simp [machineStep, hprogram, hsome]
  exact hrun t le_rfl

/-- The fixed target program performs one indexed Finset update and immediately
queries the resulting canonical bit vector. Under exact oracle semantics, its
branch is precisely the selected matroid's independence predicate. -/
theorem solution {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (i : Fin n)
    (value which : Bool) (O : IndependenceOracle n)
    (hExact : ExactOracles M₁ M₂ O) (bits : ℕ → Bool)
    (c : MachineConfig 2 11)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate i.val true)
    (h8 : c.registers 8 = []) :
    let S := if value then insert i I else I.erase i
    let out := execution (setFinsetQueryProgram value which) O c bits
      (5 * i.val + 6)
    out.control.val = (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      out.registers 6 = finsetMembershipBits S ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls + 1 ∧
      out.bitOperations = c.bitOperations + (5 * i.val + 5) + (2 * n + 1) := by
  let S : Finset (Fin n) := if value then insert i I else I.erase i
  let P : Program 2 11 := setMembershipBitProgram value ⟨11, by omega⟩
  let Q : Program 2 11 := setFinsetQueryProgram value which
  let t := 5 * i.val + 5
  have hset := setMembershipBitProgram_finset_correct value ⟨11, by omega⟩
    O bits c I i hc ho h6 h7 h8
  have hcontrol : (execution P O c bits t).control.val = 11 := by
    simpa [P, t] using congrArg Fin.val hset.1
  have hregs6 : (execution P O c bits t).registers 6 = finsetMembershipBits S := by
    simpa [P, S, t] using hset.2.1
  have hregs7 : (execution P O c bits t).registers 7 = [] := by
    simpa [P, t] using hset.2.2.1
  have hregs8 : (execution P O c bits t).registers 8 = [] := by
    simpa [P, t] using hset.2.2.2.1
  have hout : (execution P O c bits t).output = none := by
    simpa [P, t] using hset.2.2.2.2.1
  have hcalls : (execution P O c bits t).oracleCalls = c.oracleCalls := by
    simpa [P, t] using hset.2.2.2.2.2.1
  have hcost : (execution P O c bits t).bitOperations = c.bitOperations + t := by
    simpa [P, t] using hset.2.2.2.2.2.2
  have hagree : ∀ q : Fin 12, q ≠ (⟨11, by omega⟩ : Fin 12) → P q = Q q := by
    intro q hq
    simp only [P, Q, setFinsetQueryProgram]
    have hval : q.val ≠ 11 := by intro h; exact hq (Fin.ext h)
    simp [hval]
  have hhalt : P ⟨11, by omega⟩ = .halt := by
    simp [P, setMembershipBitProgram, membershipBitProgram]
  have hsame := execution_eq_away_from_halt P Q O c bits t
    ⟨11, by omega⟩ hagree hhalt hout
  have hsame' : execution Q O c bits t = execution P O c bits t := hsame.symm
  let c₁ := execution Q O c bits t
  have hc₁ : c₁.control.val = 11 := by
    simpa [c₁] using (congrArg (fun x => x.control.val) hsame').trans hcontrol
  have hregs6₁ : c₁.registers 6 = finsetMembershipBits S := by
    simpa [c₁] using (congrArg (fun x => x.registers 6) hsame').trans hregs6
  have hregs7₁ : c₁.registers 7 = [] := by
    simpa [c₁] using (congrArg (fun x => x.registers 7) hsame').trans hregs7
  have hregs8₁ : c₁.registers 8 = [] := by
    simpa [c₁] using (congrArg (fun x => x.registers 8) hsame').trans hregs8
  have hout₁ : c₁.output = none := by
    simpa [c₁] using (congrArg MachineConfig.output hsame').trans hout
  have hcalls₁ : c₁.oracleCalls = c.oracleCalls := by
    simpa [c₁] using (congrArg MachineConfig.oracleCalls hsame').trans hcalls
  have hcost₁ : c₁.bitOperations = c.bitOperations + t := by
    simpa [c₁] using (congrArg MachineConfig.bitOperations hsame').trans hcost
  let q : Fin n → Bool := fun j => decide (j ∈ S)
  have hlen : (finsetMembershipBits S).length = n := by simp [finsetMembershipBits]
  have hsetEq : {j : Fin n | q j = true} = (S : Set (Fin n)) := by
    ext j
    simp [q, finsetMembershipBits]
  have hExactQ := hExact which q
  have hOracle : O which q = decide ((if which then M₂ else M₁).Indep (S : Set (Fin n))) := by
    by_cases hi : (if which then M₂ else M₁).Indep (S : Set (Fin n))
    · have htrue : O which q = true := hExactQ.mpr (by simpa [hsetEq] using hi)
      simp [htrue, hi]
    · have hfalse : O which q = false := by
        cases hq : O which q with
        | false => rfl
        | true => exact (hi (by simpa [hsetEq] using hExactQ.mp hq)).elim
      simp [hfalse, hi]
  have hqReg : c₁.registers 6 = List.ofFn q := by
    simpa [q, finsetMembershipBits] using hregs6₁
  have hqueryStep :
      (machineStep Q O (bits t) c₁).control.val =
        (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      (machineStep Q O (bits t) c₁).oracleCalls = c₁.oracleCalls + 1 ∧
      (machineStep Q O (bits t) c₁).bitOperations = c₁.bitOperations + (2 * n + 1) ∧
      (machineStep Q O (bits t) c₁).registers 6 = c₁.registers 6 ∧
      (machineStep Q O (bits t) c₁).registers 7 = [] ∧
      (machineStep Q O (bits t) c₁).registers 8 = [] ∧
      (machineStep Q O (bits t) c₁).output = none := by
    have hprogram : Q c₁.control =
        .query which ⟨6, by omega⟩ ⟨10, by omega⟩ ⟨11, by omega⟩ := by
      simp [Q, setFinsetQueryProgram, hc₁]
    let targetControl : Fin 12 :=
      if (if which then M₂ else M₁).Indep (S : Set (Fin n))
      then ⟨11, by omega⟩ else ⟨10, by omega⟩
    have hstep := show machineStep Q O (bits t) c₁ =
        { c₁ with
          control := targetControl
          oracleCalls := c₁.oracleCalls + 1
          bitOperations := c₁.bitOperations + (2 * n + 1) } by
      simp [machineStep, hprogram, hout₁, hqReg, hOracle, hlen, targetControl]
      omega
    rw [hstep]
    constructor
    · by_cases hIndep : (if which then M₂ else M₁).Indep (S : Set (Fin n))
      · simp [targetControl, hIndep]
      · simp [targetControl, hIndep]
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · rfl
    constructor
    · exact hregs7₁
    constructor
    · exact hregs8₁
    · exact hout₁
  have hrunQ : execution Q O c bits (t + 1) = machineStep Q O (bits t) c₁ := by
    simp [c₁, execution]
  change (let out := execution Q O c bits (t + 1)
    out.control.val = (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      out.registers 6 = finsetMembershipBits S ∧ out.registers 7 = [] ∧
      out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls + 1 ∧
      out.bitOperations = c.bitOperations + t + (2 * n + 1))
  dsimp only
  rw [hrunQ]
  refine ⟨hqueryStep.1, ?_, hqueryStep.2.2.2.2.1,
    hqueryStep.2.2.2.2.2.1, hqueryStep.2.2.2.2.2.2, ?_, ?_⟩
  · exact hqueryStep.2.2.2.1.trans hregs6₁
  · rw [hqueryStep.2.1, hcalls₁]
  · rw [hqueryStep.2.2.1, hcost₁]

