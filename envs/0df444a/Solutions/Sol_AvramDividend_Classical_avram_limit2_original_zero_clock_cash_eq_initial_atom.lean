-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_zero_clock_cash_eq_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:18:02.254796+00:00
-- url     : https://prove2.me/submissions/1aeacac6-c974-44ea-9405-6b87f4c9dd1e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in ({0} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  have hCash (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (0 : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [paymentTimes_min_zero_eq_singleton_zero (ruinTime X x D ω)]
  simp_rw [hCash]
