-- Prove2me | solution 17 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:13:32.434928+00:00
-- url     : https://prove2.me/submissions/d31415e0-42d0-4793-b686-fd1adc35954c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_drift_discarded_real_to_closed_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Connect the original uniform BV stochastic source to public closed cash. -/
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
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    exact
      avram_wave7_09_corrected_positive_cap_bv_parent_zero_horizon_full_stieltjes_bound
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hxc D hD hw_nonneg
  · obtain ⟨u, hgrid, hmono, huniform⟩ :=
      avram_a19_physical_strict_horizon_uniform_grid T hpos
    have hSource :=
      avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump T hpos u
        hgrid hmono huniform
    dsimp only at hSource
    obtain ⟨M, Err, hM, hErrInt, hErrMean, hPhysical⟩ := hSource
    apply avram_bv_route11_drift_discarded_real_to_closed_cash
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x hx hxc D hD hjump T hpos
    dsimp only
    refine ⟨M, Err, ?_, hErrInt, hErrMean, ?_⟩
    · intro n
      exact ⟨(hM n).1, le_of_eq (hM n).2⟩
    · exact hPhysical
