-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_corrected_ubv_three_closed_branches
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:20:25.415468+00:00
-- url     : https://prove2.me/submissions/9e95d009-6169-4462-85a0-5d95f91940ef

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hBranch : C = 0 ∨ T = 0 ∨ (∀ᵐ ω ∂P, ruinTime X x D ω = 0)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  rcases hBranch with hC | hTzero | hRuin
  · subst C
    exact avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
      X hBV w hw0 x hxc D hD q T hT
  · subst T
    have hwC1 : ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      hw_smooth.of_le (by norm_num)
    exact avram_wave3_04_corrected_ubv_zero_horizon_bound
      X q x w C hw0 hw_cont hwC1 hw_grad D hD hxc hjump
  · have hwC1 : ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      hw_smooth.of_le (by norm_num)
    exact avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound
      X q x w C hw0 hw_cont hwC1 hw_grad D hD hxc hjump hRuin T hT
