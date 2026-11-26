-- Prove2me | solution 1 for ClassicalComplexWPT.exists_normalizedAnalyticCoefficientMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:12:41.91679+00:00
-- url     : https://prove2.me/submissions/9cc1c074-f670-453a-a8b1-304a8d965837

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_exists_radius_normalizedOrigin_close_half
import Theorems.Thm_ClassicalComplexWPT_eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
import Theorems.Thm_ClassicalComplexWPT_analyticNormalizedCoefficientMap_zero
import Theorems.Thm_ClassicalComplexWPT_analyticAt_analyticNormalizedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_analyticAt_weightedCoefficientSeries_sum


set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
      AnalyticAt ℂ (analyticNormalizedCoefficientMap p r hr d) 0 ∧
      ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ < (1 : ℝ) / 2 ∧
      ∀ᶠ z in 𝓝 (0 : Base n),
        ‖analyticNormalizedCoefficientMap p r hr d z - monomialSeq d‖ < 1 := by
  obtain ⟨r, hr, hr0, htop, hclose⟩ :=
    exists_radius_normalizedOrigin_close_half p hp horder
  have hzero : analyticNormalizedCoefficientMap p r hr d 0 =
      normalizedOriginCoeffs p r hr d :=
    analyticNormalizedCoefficientMap_zero p r hr d
  have hclose' :
      ‖analyticNormalizedCoefficientMap p r hr d 0 - monomialSeq d‖ < (1 : ℝ) / 2 := by
    rw [hzero]
    exact hclose
  have han := analyticAt_analyticNormalizedCoefficientMap p r hr d
  refine ⟨r, hr, hr0, htop, han, hclose', ?_⟩
  exact eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
    (weightedCoefficientSeries p r).sum (originWeightedCoeffs p r hr d)
    (analyticAt_weightedCoefficientSeries_sum p r hr) hclose'
end ClassicalComplexWPT
