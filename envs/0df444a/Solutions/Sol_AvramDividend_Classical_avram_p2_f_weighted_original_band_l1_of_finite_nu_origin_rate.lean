-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_band_l1_of_finite_nu_origin_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:07:35.462424+00:00
-- url     : https://prove2.me/submissions/a1e85f7d-a21d-497d-babd-776fe7f7d940

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The source-original adapted weighted count has finite first moment
when the independent zero-origin ν rate and finite ν-mark intensity hold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (hOrigin : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) = ((T : ℝ≥0∞) * X.ν B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hνfinite : X.ν B ≠ ∞) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) ≠ ∞ := by
  have hTfinite : (T : ℝ≥0∞) ≠ ∞ := by simp
  have hRateFinite : (T : ℝ≥0∞) * X.ν B ≠ ∞ :=
    ENNReal.mul_ne_top hTfinite hνfinite
  rw [avram_p2_f_weighted_original_origin_mean_to_adapted_lintegral
    X s T B hB H hH ((T : ℝ≥0∞) * X.ν B) hOrigin]
  exact ENNReal.mul_ne_top hHfinite hRateFinite
