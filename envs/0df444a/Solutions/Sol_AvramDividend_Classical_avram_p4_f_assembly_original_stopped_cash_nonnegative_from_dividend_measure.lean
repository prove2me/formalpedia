-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:01:56.213071+00:00
-- url     : https://prove2.me/submissions/c97a6b97-3a15-4c2a-9fe9-df779667aaf9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact canonical original discounted Stieltjes cash is nonnegative,
    including all atoms and singular-continuous payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 ≤ Cash ω := by
  intro ω
  rw [hCash ω]
  exact ENNReal.toReal_nonneg