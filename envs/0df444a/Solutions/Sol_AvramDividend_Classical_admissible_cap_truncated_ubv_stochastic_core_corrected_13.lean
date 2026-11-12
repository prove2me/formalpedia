-- Prove2me | solution 13 for AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:53:50.695361+00:00
-- url     : https://prove2.me/submissions/2399e804-dc26-46d0-ae32-a8c371119ea0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_actual_stopped_HJB_cash_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original capped UBV cash needs only the genuine bounded stopped-clock source budget. -/
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
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  by_cases hTzero : T = 0
  · exact avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
      X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hxc D hD hw_nonneg hjump T hT (Or.inr hTzero)
  · apply avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
      X hBV q w C hw0 x hxc D hD T hT
    intro hx
    left
    obtain ⟨n, hnT⟩ := exists_nat_gt T
    refine ⟨n, hnT, ?_⟩
    have hn : 0 < n := by
      exact_mod_cast (lt_of_le_of_lt hT hnT)
    have hC : 0 < C :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hx) hxc
    exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
      X q x D n hn T).trans
      (avram_wave7_08_source_actual_stopped_HJB_cash_budget
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn)
