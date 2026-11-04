-- Prove2me | solution 8 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:38:12.533179+00:00
-- url     : https://prove2.me/submissions/07420b2b-0457-46c0-bb4a-4ba1db911329
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_physical_envelope_branch
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_real_budget_to_ennreal
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
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  by_cases hEnvelope : x + T * X.drift ≤ w x
  · exact avram_wave7_09_corrected_positive_cap_bv_parent_physical_envelope_branch
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hxc D hD hw_nonneg T hT hEnvelope
  · have hTpos : 0 < T :=
      (avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
        X C hC w hw_cont hw0 hw_smooth hw_grad
        x hx hxc T hT hEnvelope).2.2.1
    have hSigned :=
      avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
    have hMean :=
      (avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
        X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
        x D hD T hT hTpos).2
    dsimp at hSigned hMean
    let S : ℝ≥0 := ⟨T,hT⟩
    have hTermNonneg :
        0 ≤ ∫ ω,
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) *
              w (x + X.X S ω - rightLimit D S ω) else 0) ∂P := by
      rw [hMean]
      apply integral_nonneg
      intro ω
      positivity
    have hReal :
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
          w x := by
      linarith
    exact avram_wave7_03_original_full_clock_real_budget_to_ennreal
      X x C D hD T hT q (w x) hReal
