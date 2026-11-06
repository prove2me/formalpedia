-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_grid4_original_strict_horizon_payoff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:55:03.858133+00:00
-- url     : https://prove2.me/submissions/9260e5f1-33fe-4c8d-a601-8dfc04ee54b5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual strict pre-ruin cash and surviving reserve terminal are nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (ω : Ω) :
    let S : ℝ≥0 := ⟨T, hT⟩
    0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
           ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
           Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) := by
  dsimp
  apply add_nonneg ENNReal.toReal_nonneg
  split_ifs with hsurvive
  · exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (hw_nonneg ω ⟨T, hT⟩ hTpos hsurvive)
  · exact le_refl 0
