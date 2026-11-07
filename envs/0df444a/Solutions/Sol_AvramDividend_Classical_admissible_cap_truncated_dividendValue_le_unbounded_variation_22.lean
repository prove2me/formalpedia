-- Prove2me | solution 22 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:09:53.2166+00:00
-- url     : https://prove2.me/submissions/808bf44e-8e5e-4656-8f19-6be713c48ada
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_core_corrected
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_right_payment_secant_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    obtain ⟨hI, hMax⟩ := hw_hjb y hy hyC
    exact ⟨hI, (max_le_iff.mp (le_of_eq hMax)).1⟩
  have hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hMax := (hw_hjb y hy hyC).2
    have hLe := (max_le_iff.mp (le_of_eq hMax)).2
    linarith
  have hC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht0 ht
    exact avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
      X x C hC hxc D hD w hw0 hw_cont hC1 hgrad ω t ht
  have hJump :=
    avram_sweep16_20261106_original_right_payment_secant_from_gradient
      X x C hC hxc D hD w hw_cont hw_smooth hgrad
  exact admissible_cap_truncated_ubv_stochastic_core_corrected
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth
    hgen hgrad x hxc D hD hNonneg hJump T hT
