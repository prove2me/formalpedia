-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_prebudget_expectation_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:54:17.164146+00:00
-- url     : https://prove2.me/submissions/df3540b2-e760-44db-8c77-37191a4a44cc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_prebudget_payoff_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The exact original strict-horizon stopped BV payoff has nonnegative
expectation, using the previously proved pathwise lower envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    0 ≤ (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) := by
  dsimp
  apply integral_nonneg
  intro ω
  exact avram_p3_bv_original_strict_prebudget_payoff_nonnegative
    X q T hT hTpos w x D hw_nonneg ω
