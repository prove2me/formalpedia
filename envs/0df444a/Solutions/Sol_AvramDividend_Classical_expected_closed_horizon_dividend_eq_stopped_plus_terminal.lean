-- Prove2me | solution 1 for AvramDividend.Classical.expected_closed_horizon_dividend_eq_stopped_plus_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:55:16.456626+00:00
-- url     : https://prove2.me/submissions/b4a0d032-0613-4f08-b9b3-6be36de1d4e9

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The exact closed finite-horizon expected dividend reward is the
    expectation of the strictly stopped reward plus its terminal atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Set.Iic T,
       ENNReal.ofReal (Real.exp (-(q * t)))
         ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω,
      (∫⁻ t in paymentTimes
        (min (σ ω) (ENNReal.ofReal T)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (σ ω) ∩ ({T} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ∂P) := by
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun ω =>
    paymentTimes_closed_horizon_lintegral_eq_stopped_add_atom
      (dividendMeasure D ω)
      (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
      (σ ω) T hT)
