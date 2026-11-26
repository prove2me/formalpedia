-- Prove2me | solution 1 for ClassicalComplexWPT.eval_preparedPolynomialSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:26.034688+00:00
-- url     : https://prove2.me/submissions/df95249e-a1af-4863-99f5-9bcfaa1980ff

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Theorems.Thm_ClassicalComplexWPT_constantOneSeq_apply
import Theorems.Thm_ClassicalComplexWPT_convolution_constantOneSeq
import Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_apply_fin
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_preparedTailSeq
import Theorems.Thm_ClassicalComplexWPT_seqLowShift_constantOneSeq
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_add_local
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_monomialSeq
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
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


attribute [local simp] ClassicalComplexWPT.constantOneSeq_apply
attribute [local simp] ClassicalComplexWPT.convolution_constantOneSeq
attribute [local simp] ClassicalComplexWPT.preparedTailSeq_apply_fin
attribute [local simp] ClassicalComplexWPT.seqHighShift_preparedTailSeq

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (a : Fin d → Base n → ℂ) (z : Base n) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (seqLowShift d constantOneSeq + preparedTailSeq r d a z) w =
      (((r : ℂ) ^ d)⁻¹) * preparedPolynomial d a (z, (r : ℂ) * w) := by
  rw [evalL1PowerSeries_add_local, seqLowShift_constantOneSeq,
    evalL1PowerSeries_monomialSeq d hw]
  rw [evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero d _
    (seqHighShift_preparedTailSeq r a z) hw]
  rw [preparedPolynomial]
  simp only [preparedTailSeq_apply_fin, mul_pow]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hrC), one_mul]
  · apply Finset.sum_congr rfl
    intro i hi
    ring
end ClassicalComplexWPT
