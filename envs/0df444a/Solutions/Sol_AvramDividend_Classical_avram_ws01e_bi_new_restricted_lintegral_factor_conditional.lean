-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_restricted_lintegral_factor_conditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:42:26.649959+00:00
-- url     : https://prove2.me/submissions/15820445-9405-4fae-ad9f-e28aded249f0

import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Inv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- A finite event factor cancels under positive-mass conditioning. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hApos : P A ≠ 0)
    (f : Ω → ℝ≥0∞)
    (hFactor : (∫⁻ ω in A, f ω ∂P) = P A * (∫⁻ ω, f ω ∂P)) :
    (∫⁻ ω, f ω ∂(P[|A])) = ∫⁻ ω, f ω ∂P := by
  rw [ProbabilityTheory.cond, lintegral_smul_measure]
  change (P A)⁻¹ * (∫⁻ ω in A, f ω ∂P) = _
  rw [hFactor, ← mul_assoc, ENNReal.inv_mul_cancel hApos (measure_ne_top P A),
    one_mul]
