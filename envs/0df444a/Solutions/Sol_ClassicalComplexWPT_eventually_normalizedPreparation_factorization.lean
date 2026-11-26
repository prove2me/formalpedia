-- Prove2me | solution 1 for ClassicalComplexWPT.eventually_normalizedPreparation_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:52.736804+00:00
-- url     : https://prove2.me/submissions/b856ee24-2c7d-4e4d-bc12-28f1838df2f8

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_convolution_monomialSeq
import Theorems.Thm_ClassicalComplexWPT_analyticAt_weightedCoefficientSeries_sum
import Theorems.Thm_ClassicalComplexWPT_eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionGlobal_factorization
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



set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hclose : ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ <
      (1 : ℝ) / 2) :
    ∀ᶠ z in 𝓝 (0 : Base n),
      monomialSeq d = convolution (normalizedPreparationQuotient p r hr d z)
          (analyticNormalizedCoefficientMap p r hr d z) +
        normalizedPreparationRemainder p r hr d z ∧
      seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0 := by
  have hsmall := eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
    (weightedCoefficientSeries p r).sum (originWeightedCoeffs p r hr d)
    (analyticAt_weightedCoefficientSeries_sum p r hr) hclose
  filter_upwards [hsmall] with z hz
  let tail := normalizedPreparationTail p r hr d z
  let q := normalizedPreparationQuotient p r hr d z
  let rem := normalizedPreparationRemainder p r hr d z
  have hfac := seqDivisionGlobal_factorization d tail (monomialSeq d) hz
  have hsupp := seqHighShift_divisionRemainderGlobal d tail (monomialSeq d) hz
  have hG : analyticNormalizedCoefficientMap p r hr d z = monomialSeq d + tail := by
    dsimp only [tail, normalizedPreparationTail]
    abel
  have hconv : convolution q (analyticNormalizedCoefficientMap p r hr d z) =
      seqLowShift d q + convolution q tail := by
    rw [hG, convolution_add_right, convolution_monomialSeq]
  refine ⟨?_, ?_⟩
  · rw [hconv]
    simpa only [q, rem, tail, normalizedPreparationQuotient,
      normalizedPreparationRemainder, add_assoc] using hfac
  · simpa only [rem, tail, normalizedPreparationRemainder] using hsupp
end ClassicalComplexWPT
