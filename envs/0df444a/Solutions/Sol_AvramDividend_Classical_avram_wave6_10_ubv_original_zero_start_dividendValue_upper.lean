-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_ubv_original_zero_start_dividendValue_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:21:48.284206+00:00
-- url     : https://prove2.me/submissions/7d036925-e464-4a2f-8a1b-3af7704dddf4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X 0 D t ω) -
          w (riskProcess X 0 D t ω -
            (rightLimit D t ω - D t ω))) :
    dividendValue X q 0 D ≤ ENNReal.ofReal (w 0) := by
  apply dividendValue_le_of_uniform_truncated_bounds
    X q 0 D hD.1 (ENNReal.ofReal (w 0))
  intro n
  exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
    X hBV q w C hw0 hw_cont hw_smooth hw_grad D hD hjump
    (n : ℝ) (Nat.cast_nonneg n)
