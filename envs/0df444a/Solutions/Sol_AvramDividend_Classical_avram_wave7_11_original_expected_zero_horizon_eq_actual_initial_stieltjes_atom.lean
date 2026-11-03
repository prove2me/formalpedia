-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_zero_horizon_eq_actual_initial_stieltjes_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:08:22.254025+00:00
-- url     : https://prove2.me/submissions/f98916eb-f0ac-4378-8277-a838735575c0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine original expected dividend payout at horizon zero is
    precisely the expected source time-zero right-payment atom, irrespective
    of the ruin clock or discount rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, (dividendMeasure D ω) ({0} : Set ℝ) ∂P) := by
  apply lintegral_congr
  intro ω
  exact avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
    D ω (ruinTime X x D ω) q
