-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_all_caps_source_ubv_value_from_one_future_clock_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:31:56.245571+00:00
-- url     : https://prove2.me/submissions/f3b837e2-8ee5-4a40-8f26-05f0a5844af0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_cap_original_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_source_ubv_value_from_one_future_clock_budget
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact original UBV finite-horizon dividend verification for all caps:
    zero cap is handled by corrected initial-cash control, and positive
    cap requires only one strictly future natural clock budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hOneClock : 0 < C → 0 < x →
      ∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ C) with hzero | hpositive
  · subst C
    have hsmooth :
        (¬ X.BoundedVariation →
          ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (0 : ℝ≥0∞)}) ∧
        (X.BoundedVariation →
          ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (0 : ℝ≥0∞)}) :=
      ⟨fun _ => hw_smooth, fun hbv => (hBV hbv).elim⟩
    obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
      local_verification_stochastic_core_side_conditions
        X q w 0 hw_cont hw0 hsmooth hw_hjb x hxc D hD
    exact avram_wave7_11_zero_cap_original_stieltjes_bound
      X hBV q w hw0 hw_cont hw_smooth hgrad x hx hxc D hD hjump T hT
  · exact avram_wave7_11_source_ubv_value_from_one_future_clock_budget
      X hX hBV q hq w C hpositive hw_cont hw0 hw_neg hw_smooth
      hw_hjb x hx hxc D hD T hT (hOneClock hpositive)
