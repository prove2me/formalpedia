-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave6_chat05_ubv_positive_initial_uniform_ruin_clock_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:57:49.040385+00:00
-- url     : https://prove2.me/submissions/ad3c0cf8-0e21-4ab8-a6bc-155a10a519fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_clock_source_dividend_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_positive_n_zero_horizon_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
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
    (T : ℝ) (hT : 0 ≤ T) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
  have hC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  intro n
  cases n with
  | zero =>
      simpa only [Nat.cast_zero] using
        (avram_wave7_08_zero_clock_source_dividend_budget
          X q x w C hw0 hw_cont hC1 hw_grad D hD hxc hjump T)
  | succ k =>
      by_cases hTpos : 0 < T
      · exact
          avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
            X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
            x hx hxc D hD hw_nonneg hjump T hTpos (k + 1) (by omega)
      · have hTzero : T = 0 := le_antisymm (le_of_not_gt hTpos) hT
        subst T
        exact
          avram_wave7_08_positive_n_zero_horizon_source_budget
            X q x w C hw0 hw_cont hC1 hw_grad D hD hxc hjump
            (k + 1) (by omega)
