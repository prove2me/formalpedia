-- Prove2me | solution 1 for ClassicalComplexWPT.preparedPolynomial_preparationCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:48.129692+00:00
-- url     : https://prove2.me/submissions/2030d091-1852-43f1-a6d3-f5a7d5dfb200

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_zero
import Theorems.Thm_ClassicalComplexWPT_weighted_scaled_pow
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


attribute [local simp] ClassicalComplexWPT.evalL1PowerSeries_zero

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) (hr0 : 0 < r)
    (z : Base n) (w : ℂ) :
    preparedPolynomial d (preparationCoefficient p r hr d) (z, w) =
      (r : ℂ) ^ d *
        ((r : ℂ)⁻¹ ^ d * w ^ d -
          ∑ i : Fin d, normalizedPreparationRemainder p r hr d z i *
            ((r : ℂ)⁻¹ * w) ^ (i : ℕ)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hrpow : (r : ℂ) ^ d * (r : ℂ)⁻¹ ^ d = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hrC, one_pow]
  have hlead : (r : ℂ) ^ d * ((r : ℂ)⁻¹ ^ d * w ^ d) = w ^ d := by
    rw [← mul_assoc, hrpow, one_mul]
  rw [preparedPolynomial]
  simp only [preparationCoefficient]
  rw [mul_sub, hlead, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hs := weighted_scaled_pow (r : ℂ) hrC i.isLt.le w
  calc
    (-((r : ℂ) ^ (d - (i : ℕ))) *
          normalizedPreparationRemainder p r hr d z i) * w ^ (i : ℕ) =
        -(normalizedPreparationRemainder p r hr d z i *
          ((r : ℂ) ^ (d - (i : ℕ)) * w ^ (i : ℕ))) := by ring
    _ = -(normalizedPreparationRemainder p r hr d z i *
          ((r : ℂ) ^ d * ((r : ℂ)⁻¹ * w) ^ (i : ℕ))) := by rw [hs]
    _ = -((r : ℂ) ^ d *
          (normalizedPreparationRemainder p r hr d z i *
            ((r : ℂ)⁻¹ * w) ^ (i : ℕ))) := by ring
end ClassicalComplexWPT
