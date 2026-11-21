-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a563_ubv_positive_reserve_original_dividendValue_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:58:46.984234+00:00
-- url     : https://prove2.me/submissions/1491f424-4dab-4b52-9829-5c8ff7028e65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_uniform_positive_source_to_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_ga_a570_positive_UBV_true_bounded_ruin_clock_Ito_witness
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    obtain ⟨hi, hm⟩ := hw_hjb y hy hyC
    exact ⟨hi, (le_max_left _ _).trans_eq hm⟩
  have hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hm := (hw_hjb y hy hyC).2
    have hh : 1 - deriv w y ≤ 0 := (le_max_right _ _).trans_eq hm
    linarith
  have hEvidence :=
    AvramDividend.Classical.avram_ga_a570_positive_UBV_true_bounded_ruin_clock_Ito_witness
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hx hxc D hD hxpos
  exact AvramDividend.Classical.avram_limit1_ubv_uniform_positive_source_to_dividendValue
    X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hgrad
    x hxc D hD hEvidence
