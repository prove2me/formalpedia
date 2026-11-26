-- Prove2me | solution 1 for ClassicalComplexWPT.normalizedPreparationQuotient_zero_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:03.034931+00:00
-- url     : https://prove2.me/submissions/be1ac7bc-89f5-489b-a5c8-207ba5470c2c

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_convolution_apply_eq_zero_of_right
import Theorems.Thm_ClassicalComplexWPT_normalizedPreparationTail_zero_of_le
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotientGlobal_eq
import Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotient_equation
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainderGlobal
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply



set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ}
    {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1) :
    normalizedPreparationQuotient p r hr d 0 0 = 1 := by
  rw [normalizedPreparationQuotient, seqDivisionQuotientGlobal_eq d _ _ hsmall]
  have heq := seqDivisionQuotient_equation d
    (normalizedPreparationTail p r hr d 0) hsmall (monomialSeq d)
  have hconv : convolution
      (seqDivisionQuotient d (normalizedPreparationTail p r hr d 0) hsmall
        (monomialSeq d)) (normalizedPreparationTail p r hr d 0) d = 0 := by
    exact convolution_apply_eq_zero_of_right (fun j hj ↦
      normalizedPreparationTail_zero_of_le p hp horder r hr0 hr hj)
  have hcoord := congrArg (fun s : OriginSeq ↦ s 0) heq
  simp only [lp.coeFn_add, Pi.add_apply, seqHighShift_apply, zero_add] at hcoord
  rw [hconv, monomialSeq_apply_same, add_zero] at hcoord
  exact hcoord
end ClassicalComplexWPT
