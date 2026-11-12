-- Prove2me | solution 3 for AvramDividend.Classical.avram_wave7_08_ubv_positive_reserve_positive_horizon_source_ito_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:17:33.346122+00:00
-- url     : https://prove2.me/submissions/0a433631-80e4-459c-983c-527660483cb5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_actual_stopped_HJB_cash_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The positive-horizon original bound reduces to one physical stopped cash estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  apply avram_wave7_11_admissible_initial_reserve_either_clock_ubv_value
    X hBV q w C hw0 x hxc D hD T (le_of_lt hT)
  intro _
  left
  obtain ⟨n, hnT⟩ := exists_nat_gt T
  refine ⟨n, hnT, ?_⟩
  have hn : 0 < n := by
    have hnreal : (0 : ℝ) < (n : ℝ) := lt_trans hT hnT
    exact_mod_cast hnreal
  exact (avram_wave7_08_truncated_cash_le_actual_stopped_clock
    X q x D n hn T).trans
    (avram_wave7_08_source_actual_stopped_HJB_cash_budget
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn)
