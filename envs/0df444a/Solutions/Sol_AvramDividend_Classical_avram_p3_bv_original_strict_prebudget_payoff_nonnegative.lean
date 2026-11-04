-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_prebudget_payoff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:40:26.005925+00:00
-- url     : https://prove2.me/submissions/1953e62d-caa7-4164-b0e1-a664fb1dfad7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
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
  split_ifs with hSurvive
  · have hSpos : (0 : ℝ≥0) < ⟨T, hT⟩ := by
      exact_mod_cast hTpos
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (hw_nonneg ω ⟨T, hT⟩ hSpos hSurvive)
  · exact le_refl 0
