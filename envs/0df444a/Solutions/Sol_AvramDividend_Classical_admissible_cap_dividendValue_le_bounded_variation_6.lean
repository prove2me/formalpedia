-- Prove2me | solution 6 for AvramDividend.Classical.admissible_cap_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:18:43.410472+00:00
-- url     : https://prove2.me/submissions/75f02456-1a82-4d02-8ef3-31cb6b78ae57
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_nat_horizon_bound_bounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original full Stieltjes dividend-value bound follows from
the canonical natural-horizon BV budget by monotone convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hNat :
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
            paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) :=
    admissible_cap_nat_horizon_bound_bounded_variation
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_hjb x hx hxc D hD
  exact avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
    X q x D hD.1 (ENNReal.ofReal (w x)) hNat
