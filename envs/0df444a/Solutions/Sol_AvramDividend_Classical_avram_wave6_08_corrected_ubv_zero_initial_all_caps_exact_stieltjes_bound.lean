-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:03:16.446062+00:00
-- url     : https://prove2.me/submissions/96ed7333-61a7-4a8f-81bc-e67a1b4676f3

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

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
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w 0) := by
  have hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hruin : ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 :=
    avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae X hBV D hD.1.1
  have hxc : ENNReal.ofReal (0 : ℝ) ≤ C := by simp
  exact avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound
    X q 0 w C hw0 hw_cont hwC1 hw_grad D hD hxc hjump hruin T hT
