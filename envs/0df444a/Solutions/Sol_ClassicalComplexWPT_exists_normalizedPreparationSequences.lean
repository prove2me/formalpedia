-- Prove2me | solution 1 for ClassicalComplexWPT.exists_normalizedPreparationSequences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:37:01.668802+00:00
-- url     : https://prove2.me/submissions/093beab0-6b65-4f23-9ef2-8f6666afc95a

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedPreparationQuotient
import Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedPreparationRemainder
import Theorems.Thm_ClassicalComplexWPT_eventually_normalizedPreparation_factorization
import Theorems.Thm_ClassicalComplexWPT_normalizedPreparationRemainder_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedPreparationQuotient_zero_apply_zero
import Theorems.Thm_ClassicalComplexWPT_exists_normalizedAnalyticCoefficientMap


set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
      AnalyticAt ℂ (normalizedPreparationQuotient p r hr d) 0 ∧
      AnalyticAt ℂ (normalizedPreparationRemainder p r hr d) 0 ∧
      (∀ᶠ z in 𝓝 (0 : Base n),
        monomialSeq d = convolution (normalizedPreparationQuotient p r hr d z)
            (analyticNormalizedCoefficientMap p r hr d z) +
          normalizedPreparationRemainder p r hr d z ∧
        seqHighShift d (normalizedPreparationRemainder p r hr d z) = 0) ∧
      normalizedPreparationRemainder p r hr d 0 = 0 ∧
      normalizedPreparationQuotient p r hr d 0 0 = 1 := by
  obtain ⟨r, hr, hr0, htop, han, hclose, hevent⟩ :=
    exists_normalizedAnalyticCoefficientMap p hp horder
  have hsmall : ‖normalizedPreparationTail p r hr d 0‖ < 1 := by
    exact hclose.trans (by norm_num)
  refine ⟨r, hr, hr0, htop,
    analyticAt_normalizedPreparationQuotient p r hr d hsmall,
    analyticAt_normalizedPreparationRemainder p r hr d hsmall,
    eventually_normalizedPreparation_factorization p r hr hclose,
    normalizedPreparationRemainder_zero p hp horder r hr0 hr hsmall,
    normalizedPreparationQuotient_zero_apply_zero p hp horder r hr0 hr hsmall⟩
end ClassicalComplexWPT
