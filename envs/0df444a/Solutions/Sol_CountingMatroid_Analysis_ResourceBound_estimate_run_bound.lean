-- Prove2me | solution 1 for CountingMatroid.Analysis.ResourceBound.estimate_run_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:47:42.370882+00:00
-- url     : https://prove2.me/submissions/bbcd0243-9a32-47db-89f4-b5a02485863d

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_boundedRun_resource_envelope
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_estimate_none_nonneg
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_estimate_none_raw_cost_bound
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_preprocess_resource_bound
import Theorems.Thm_CountingMatroid_Analysis_ScheduleResourceEnvelope_schedule_resource_envelope

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations









/-- INTERNAL: Every early answer from the pretest is nonnegative. -/
theorem preprocess_answer_nonneg (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (h : (CountingMatroid.Program.preprocess contract.implementation n r o₁ o₂).val =
      some q) : 0 ≤ q := by
  by_cases hn : n == 0
  · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn] at h
    rw [h.symm]
    norm_num
  · by_cases hf : (contract.implementation.run n r o₁ o₂).val
    · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn, hf] at h
    · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn, hf] at h
      rw [h.symm]











/-- INTERNAL: An early pretest answer is the estimator's answer, and the
estimator incurs exactly the pretest charges on that branch.
TEXLINE: main.tex:1442-1469 -/
theorem estimate_preliminary_branch (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (q : ℚ)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = some q) :
    let pre := CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂
    let run := CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape
    run.val = q ∧ oracleCalls run = oracleCalls pre ∧
      otherSteps run = otherSteps pre := by
  dsimp
  simp [CountingMatroid.Program.estimate, h, oracleCalls, otherSteps]

/-- INTERNAL: The early-answer branch already satisfies the pretest's exact
resource bounds and answer sign, independently of schedule construction.
TEXLINE: main.tex:1442-1469 -/
theorem estimate_preliminary_resource_bound (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (q : ℚ)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = some q) :
    let run := CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape
    0 ≤ run.val ∧
    oracleCalls run ≤ contract.callConstant * (n + r + 1) ^ contract.callDegree ∧
    otherSteps run ≤
      contract.bitConstant * (n + r + 1) ^ contract.bitDegree + 1 := by
  obtain ⟨hval, hcalls, hsteps⟩ :=
    estimate_preliminary_branch contract n r o₁ o₂ p tape q h
  obtain ⟨hpreCalls, hpreSteps⟩ :=
    preprocess_resource_bound contract n r o₁ o₂
  dsimp at *
  rw [hval, hcalls, hsteps]
  exact ⟨preprocess_answer_nonneg contract n r o₁ o₂ q h,
    hpreCalls, hpreSteps⟩





end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · closed the estimator cost and sign bound using the schedule and bounded-run envelopes and a proved median resource module.
* r7 · open · proved exact and bounded early-answer branches; reduced the estimator theorem to the `preprocess = none` branch, whose median scan still needs a rational-length cost invariant.
* r6 · open · split schedule arithmetic and capped-run rational invariants into independently elaborated resource envelopes; the estimator still needs median and charge composition.
* r5 · open · proved charged rational-power value and nonnegativity, and zero oracle calls for rational acceptance; the full polynomial bound still needs rational-size invariants.
* r4 · open · proved zero oracle cost for classification, bounded uniform draws, and paired selection, plus a `2*n` oracle cap for observation recording; rational-size invariants still block the full run bound.
* r3 · open · proved greedy and paired rank oracle caps and zero oracle cost of rational powers; the annealing phase still needs rational-size invariants.
* r2 · open · proved charged bind/loop and pretest resource lemmas; the annealing phase bound still needs rational-size invariants.
* r1 · open · proved support transport and added `r ≤ n`; the per-run charged polynomial bound remains unproved.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- PAPER: main.tex:1333-1440, 1455-1469
Every branch of the charged estimator, including abort branches, has a
nonnegative answer and polynomial charged costs. -/
theorem solution (contract : FeasibilityContract) :
    ∃ (C degree : ℕ), ∀ (n r : ℕ)
      (o₁ o₂ : IndependenceOracle n) (p : InputParams)
      (tape : ℕ → ℕ → Bool),
      r ≤ n →
      let run := CountingMatroid.Program.estimate contract.implementation
        n r o₁ o₂ p tape
      let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹)
      0 ≤ run.val ∧
      oracleCalls run ≤ C * (size + 1) ^ degree ∧
      otherSteps run ≤ C * (size + 1) ^ degree := by
  have hnone : ∃ (C degree : ℕ), ∀ (n r : ℕ)
      (o₁ o₂ : IndependenceOracle n) (p : InputParams)
      (tape : ℕ → ℕ → Bool), r ≤ n →
      (CountingMatroid.Program.preprocess contract.implementation
        n r o₁ o₂).val = none →
      let run := CountingMatroid.Program.estimate contract.implementation
        n r o₁ o₂ p tape
      let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹)
      0 ≤ run.val ∧
      oracleCalls run ≤ C * (size + 1) ^ degree ∧
      otherSteps run ≤ C * (size + 1) ^ degree := by
    have hcost : ∃ (C degree : ℕ), ∀ (n r : ℕ)
        (o₁ o₂ : IndependenceOracle n) (p : InputParams)
        (tape : ℕ → ℕ → Bool), r ≤ n →
        (CountingMatroid.Program.preprocess contract.implementation
          n r o₁ o₂).val = none →
        let run := CountingMatroid.Program.estimate contract.implementation
          n r o₁ o₂ p tape
        let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹)
        oracleCalls run ≤ C * (size + 1) ^ degree ∧
        otherSteps run ≤ C * (size + 1) ^ degree := by
      obtain ⟨Cs, Ds, hschedule⟩ :=
        ScheduleResourceEnvelope.schedule_resource_envelope
      obtain ⟨Cr, Dr, hbounded⟩ :=
        BoundedRunResourceEnvelope.boundedRun_resource_envelope
      let A := Cs + Cr + contract.callConstant * 2 ^ contract.callDegree +
        contract.bitConstant * 2 ^ contract.bitDegree + 10
      let D := Ds + Dr + contract.callDegree + contract.bitDegree + 10
      refine ⟨100 * A ^ (Dr + 4), D * (Dr + 4), ?_⟩
      intro n r o₁ o₂ p tape hr hpre
      let X := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let s := (CountingMatroid.Program.schedule n p).val
      let B := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      let R := Cr * B ^ Dr
      have hs := hschedule n r p
      have hrun (j : ℕ) :
          let run := CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0
          binaryRatLength run.val.1 ≤ R ∧
            oracleCalls run ≤ R ∧ otherSteps run ≤ R := by
        simpa [R, B, s] using
          (hbounded n r o₁ o₂ (tape j) s hs.1).2
      have hraw := estimate_none_raw_cost_bound contract n r o₁ o₂ p tape R
        hpre (by simpa [R, s] using hrun)
      let Q := A * X ^ D
      have hX : 1 ≤ X := by dsimp [X]; omega
      have hA : 10 ≤ A := by dsimp [A]; omega
      have hQ : 1 ≤ Q := by
        dsimp [Q]
        have hp : 1 ≤ X ^ D := one_le_pow₀ hX
        nlinarith
      have hbase : Cs * X ^ Ds ≤ Q := by
        dsimp [Q]
        exact Nat.mul_le_mul (by dsimp [A]; omega)
          (pow_le_pow_right₀ hX (by dsimp [D]; omega))
      have hB : B ≤ Q := by
        have hh := hs.2.1
        have hpart : B ≤ Cs * X ^ Ds := by
          dsimp [B, s, X] at hh ⊢
          omega
        exact le_trans hpart hbase
      have hT : s.repetitions ≤ Q := by
        have hh := hs.2.1
        dsimp [s, X] at *
        omega
      have hscheduleCalls : oracleCalls (CountingMatroid.Program.schedule n p) ≤ Q := by
        exact le_trans hs.2.2.1 hbase
      have hscheduleSteps : otherSteps (CountingMatroid.Program.schedule n p) ≤ Q := by
        exact le_trans hs.2.2.2 hbase
      have hpreBounds := preprocess_resource_bound contract n r o₁ o₂
      have h2X : n + r + 1 ≤ 2 * X := by dsimp [X]; omega
      have hpreCalls : oracleCalls (CountingMatroid.Program.preprocess
          contract.implementation n r o₁ o₂) ≤ Q := by
        calc
          _ ≤ contract.callConstant * (n + r + 1) ^ contract.callDegree :=
            hpreBounds.1
          _ ≤ contract.callConstant * (2 * X) ^ contract.callDegree :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2X _)
          _ = (contract.callConstant * 2 ^ contract.callDegree) *
              X ^ contract.callDegree := by rw [mul_pow]; ring
          _ ≤ Q := by
            dsimp [Q]
            exact Nat.mul_le_mul (by dsimp [A]; omega)
              (pow_le_pow_right₀ hX (by dsimp [D]; omega))
      have hpreSteps : otherSteps (CountingMatroid.Program.preprocess
          contract.implementation n r o₁ o₂) ≤ Q := by
        have hpow := Nat.pow_le_pow_left h2X contract.bitDegree
        have hcoeff : contract.bitConstant * (n + r + 1) ^
            contract.bitDegree + 1 ≤
            (contract.bitConstant * 2 ^ contract.bitDegree + 1) *
              X ^ contract.bitDegree := by
          have hp : 1 ≤ X ^ contract.bitDegree := one_le_pow₀ hX
          calc
            _ ≤ contract.bitConstant * (2 * X) ^ contract.bitDegree + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) 1
            _ = (contract.bitConstant * 2 ^ contract.bitDegree) *
                X ^ contract.bitDegree + 1 := by rw [mul_pow]; ring
            _ ≤ (contract.bitConstant * 2 ^ contract.bitDegree + 1) *
                X ^ contract.bitDegree := by nlinarith
        exact le_trans hpreBounds.2 (le_trans hcoeff (by
          dsimp [Q]
          exact Nat.mul_le_mul (by dsimp [A]; omega)
            (pow_le_pow_right₀ hX (by dsimp [D]; omega))))
      have hCr : Cr ≤ Q := by
        have hp : 1 ≤ X ^ D := one_le_pow₀ hX
        calc
          Cr ≤ A := by dsimp [A]; omega
          _ = A * 1 := by omega
          _ ≤ Q := by
            dsimp [Q]
            exact Nat.mul_le_mul_left A hp
      have hR : R ≤ Q ^ (Dr + 1) := by
        calc
          R = Cr * B ^ Dr := rfl
          _ ≤ Q * Q ^ Dr := Nat.mul_le_mul hCr
            (Nat.pow_le_pow_left hB Dr)
          _ = Q ^ (Dr + 1) := by rw [pow_succ]; ac_rfl
      let a := Q ^ (Dr + 1)
      let P := Q ^ (Dr + 4)
      have ha : 1 ≤ a := one_le_pow₀ hQ
      have hQP : Q ≤ P := by
        simpa [P, pow_one] using
          (pow_le_pow_right₀ hQ (by omega : 1 ≤ Dr + 4))
      have hQaP : Q * a ≤ P := by
        calc
          Q * a = Q ^ 1 * Q ^ (Dr + 1) := by simp [a]
          _ = Q ^ (1 + (Dr + 1)) := (pow_add Q 1 (Dr + 1)).symm
          _ = Q ^ (Dr + 2) := by congr 1; omega
          _ ≤ P := pow_le_pow_right₀ hQ (by omega)
      have hQ2aP : Q ^ 2 * a ≤ P := by
        calc
          Q ^ 2 * a = Q ^ 2 * Q ^ (Dr + 1) := rfl
          _ = Q ^ (2 + (Dr + 1)) := (pow_add Q 2 (Dr + 1)).symm
          _ = Q ^ (Dr + 3) := by congr 1; omega
          _ ≤ P := pow_le_pow_right₀ hQ (by omega)
      have hTplus : s.repetitions + 1 ≤ 2 * Q := by omega
      have hTplusSq : (s.repetitions + 1) ^ 2 ≤ 4 * Q ^ 2 := by
        calc
          _ ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left hTplus 2
          _ = 4 * Q ^ 2 := by
            rw [mul_pow]
            norm_num
      have hRplus : 2 * R + 8 ≤ 10 * a := by
        have hh : R ≤ a := hR
        omega
      have hmedian : (s.repetitions + 1) ^ 2 * (2 * R + 8) ≤
          40 * P := by
        calc
          _ ≤ (4 * Q ^ 2) * (10 * a) :=
            Nat.mul_le_mul hTplusSq hRplus
          _ = 40 * (Q ^ 2 * a) := by
            simpa only [show (4 : ℕ) * 10 = 40 by norm_num] using
              (mul_mul_mul_comm (4 : ℕ) (Q ^ 2) 10 a)
          _ ≤ 40 * P := Nat.mul_le_mul_left 40 hQ2aP
      have hTR : s.repetitions * R ≤ P :=
        le_trans (Nat.mul_le_mul hT hR) hQaP
      have hTR1 : s.repetitions * (R + 1) ≤ 2 * P := by
        have hRa : R + 1 ≤ 2 * a := by omega
        calc
          _ ≤ Q * (2 * a) := Nat.mul_le_mul hT hRa
          _ = 2 * (Q * a) := by
            calc
              Q * (2 * a) = (Q * 2) * a := (mul_assoc Q 2 a).symm
              _ = (2 * Q) * a := by rw [mul_comm Q 2]
              _ = 2 * (Q * a) := mul_assoc 2 Q a
          _ ≤ 2 * P := Nat.mul_le_mul_left 2 hQaP
      have hrawCalls := hraw.1
      have hrawSteps := hraw.2
      have hfinalCalls : oracleCalls (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤ 100 * P := by
        calc
          _ ≤ oracleCalls (CountingMatroid.Program.preprocess
                contract.implementation n r o₁ o₂) +
              oracleCalls (CountingMatroid.Program.schedule n p) +
              s.repetitions * R := hrawCalls
          _ ≤ Q + Q + P := by omega
          _ ≤ 100 * P := by omega
      have hfinalSteps : otherSteps (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤ 100 * P := by
        calc
          _ ≤ otherSteps (CountingMatroid.Program.preprocess
                contract.implementation n r o₁ o₂) +
              otherSteps (CountingMatroid.Program.schedule n p) +
              s.repetitions * (R + 1) +
              (s.repetitions + 1) ^ 2 * (2 * R + 8) := hrawSteps
          _ ≤ Q + Q + 2 * P + 40 * P := by omega
          _ ≤ 100 * P := by omega
      have hpoly : 100 * P =
          (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4)) := by
        calc
          100 * P = 100 * (A * X ^ D) ^ (Dr + 4) := rfl
          _ = 100 * (A ^ (Dr + 4) * (X ^ D) ^ (Dr + 4)) := by
            rw [mul_pow]
          _ = (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4)) := by
            rw [← pow_mul]
            rw [mul_assoc]
      change oracleCalls (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤
          (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4)) ∧
        otherSteps (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤
          (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4))
      rw [← hpoly]
      exact ⟨hfinalCalls, hfinalSteps⟩
    obtain ⟨C, degree, hcost⟩ := hcost
    refine ⟨C, degree, ?_⟩
    intro n r o₁ o₂ p tape hr h
    exact ⟨estimate_none_nonneg contract n r o₁ o₂ p tape h,
      hcost n r o₁ o₂ p tape hr h⟩
  obtain ⟨Cnone, Dnone, hnone⟩ := hnone
  let callCoeff := contract.callConstant * 2 ^ contract.callDegree
  let bitCoeff := contract.bitConstant * 2 ^ contract.bitDegree
  let C := Cnone + callCoeff + bitCoeff + 1
  let degree := Dnone + contract.callDegree + contract.bitDegree + 1
  refine ⟨C, degree, ?_⟩
  intro n r o₁ o₂ p tape hr
  let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹)
  let x := size + 1
  have hx : 1 ≤ x := by dsimp [x]; omega
  have hpower (c d : ℕ) (hc : c ≤ C) (hd : d ≤ degree) :
      c * x ^ d ≤ C * x ^ degree := by
    exact Nat.mul_le_mul hc (pow_le_pow_right₀ hx hd)
  by_cases hp : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = none
  · obtain ⟨hnonneg, hcalls, hsteps⟩ := hnone n r o₁ o₂ p tape hr hp
    dsimp at hnonneg hcalls hsteps ⊢
    refine ⟨hnonneg, le_trans hcalls ?_, le_trans hsteps ?_⟩
    · exact hpower Cnone Dnone (by dsimp [C]; omega)
        (by dsimp [degree]; omega)
    · exact hpower Cnone Dnone (by dsimp [C]; omega)
        (by dsimp [degree]; omega)
  · cases hq : (CountingMatroid.Program.preprocess contract.implementation
        n r o₁ o₂).val with
    | none => exact False.elim (hp hq)
    | some q =>
        obtain ⟨hnonneg, hcalls, hsteps⟩ :=
          estimate_preliminary_resource_bound contract n r o₁ o₂ p tape q hq
        dsimp at hnonneg hcalls hsteps ⊢
        have hnsize : n ≤ size := by dsimp [size]; omega
        have hbase : n + r + 1 ≤ 2 * x := by
          dsimp [x]
          omega
        have hcallPow := Nat.pow_le_pow_left hbase contract.callDegree
        have hbitPow := Nat.pow_le_pow_left hbase contract.bitDegree
        have hcall : contract.callConstant * (n + r + 1) ^ contract.callDegree ≤
            callCoeff * x ^ contract.callDegree := by
          calc
            _ ≤ contract.callConstant * (2 * x) ^ contract.callDegree :=
              Nat.mul_le_mul_left _ hcallPow
            _ = callCoeff * x ^ contract.callDegree := by
              dsimp [callCoeff]
              rw [mul_pow]
              ring
        have hbit : contract.bitConstant * (n + r + 1) ^ contract.bitDegree ≤
            bitCoeff * x ^ contract.bitDegree := by
          calc
            _ ≤ contract.bitConstant * (2 * x) ^ contract.bitDegree :=
              Nat.mul_le_mul_left _ hbitPow
            _ = bitCoeff * x ^ contract.bitDegree := by
              dsimp [bitCoeff]
              rw [mul_pow]
              ring
        refine ⟨hnonneg, le_trans hcalls (le_trans hcall ?_), ?_⟩
        · exact hpower callCoeff contract.callDegree
            (by dsimp [C]; omega) (by dsimp [degree]; omega)
        · have hbitMain : bitCoeff * x ^ contract.bitDegree ≤
              bitCoeff * x ^ degree :=
            Nat.mul_le_mul_left _ (pow_le_pow_right₀ hx
              (by dsimp [degree]; omega))
          have hone : 1 ≤ x ^ degree := one_le_pow₀ hx
          have hcoef : (bitCoeff + 1) * x ^ degree ≤ C * x ^ degree :=
            Nat.mul_le_mul_right _ (by dsimp [C]; omega)
          change otherSteps (CountingMatroid.Program.estimate
            contract.implementation n r o₁ o₂ p tape) ≤ C * x ^ degree
          calc
            _ ≤ contract.bitConstant * (n + r + 1) ^ contract.bitDegree + 1 :=
              hsteps
            _ ≤ bitCoeff * x ^ contract.bitDegree + 1 :=
              Nat.add_le_add_right hbit 1
            _ ≤ bitCoeff * x ^ degree + x ^ degree :=
              Nat.add_le_add hbitMain hone
            _ = (bitCoeff + 1) * x ^ degree := by ring
            _ ≤ C * x ^ degree := hcoef
