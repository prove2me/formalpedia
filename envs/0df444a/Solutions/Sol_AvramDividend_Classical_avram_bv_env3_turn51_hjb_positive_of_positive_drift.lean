-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn51_hjb_positive_of_positive_drift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:08:35.440212+00:00
-- url     : https://prove2.me/submissions/c784aa37-8ace-48bb-8f96-4d483bde6469
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_positive_initial_value_of_positive_reserve
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The zero-reserve BV HJB boundary positivity result and the proved
    positive-reserve secant estimate jointly cover every admissible reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (hDrift : 0 < X.drift) :
    0 < w x := by
  rcases eq_or_lt_of_le hx with hxzero | hxpos
  · simpa [hxzero.symm] using
      (avram_bv_env3_turn52_origin_value_positive_of_BV_HJB
        X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad hDrift)
  · exact avram_p3_grid4_positive_initial_value_of_positive_reserve
      C hC w hw_cont hw0 hw_smooth hw_grad x hxpos hxc
