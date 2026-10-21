-- Prove2me | solution 1 for FiniteFields.Dwork.ramifiedTeichmullerLift_norm_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:47:03.342327+00:00
-- url     : https://prove2.me/submissions/0c469da2-122a-440d-8e83-5e6834372d93

import Mathlib
import Definitions.Def_FiniteFields_Dwork_AdditiveCharacter
open scoped BigOperators WithZero
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [hpChar : CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw4eResiduePrimeAlgebra
attribute [local instance] FiniteFields.Dwork.dw4eDecidableEq
theorem solution {x : k} (hx : x ≠ 0) :
    ‖ramifiedTeichmullerLift k p x‖ = 1 := by
  rw [ramifiedTeichmullerLift, dworkCyclotomicField_norm_algebraMap]
  have hu : IsUnit (teichmullerLift k p x) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    simpa [teichmullerLift] using hx
  have hv : coefficientValuation k p
      (algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
        (teichmullerLift k p x)) = 1 :=
    Valuation.Integers.one_of_isUnit' hu
      (fun a => (IsDiscreteValuationRing.maximalIdeal
        (CoefficientRing k p)).valuation_le_one
          (K := CoefficientFractionField k p) a)
  apply le_antisymm
  · rw [Valued.toNormedField.norm_le_one_iff]
    change Valued.v
        (((WithVal.equiv (coefficientValuation k p)).symm
          (algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
            (teichmullerLift k p x)) : WithVal (coefficientValuation k p)) :
          CoefficientField k p) ≤ 1
    rw [Valued.valuedCompletion_apply]
    exact hv.le
  · rw [Valued.toNormedField.one_le_norm_iff]
    change 1 ≤ Valued.v
        (((WithVal.equiv (coefficientValuation k p)).symm
          (algebraMap (CoefficientRing k p) (CoefficientFractionField k p)
            (teichmullerLift k p x)) : WithVal (coefficientValuation k p)) :
          CoefficientField k p)
    rw [Valued.valuedCompletion_apply]
    exact hv.ge
