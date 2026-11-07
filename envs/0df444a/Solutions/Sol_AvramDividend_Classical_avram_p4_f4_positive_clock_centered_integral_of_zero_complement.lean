-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_positive_clock_centered_integral_of_zero_complement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:38:29.570102+00:00
-- url     : https://prove2.me/submissions/d3604d76-76e2-4537-8273-b64c238ddf3c

import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
/-- A centred stochastic source vanishing outside an event remains centred when restricted to that event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S) (M : Ω → ℝ)
    (hMean : (∫ ω, M ω ∂P) = 0)
    (hZeroOutside : ∀ᵐ ω ∂P, ω ∉ S → M ω = 0) :
    (∫ ω in S, M ω ∂P) = 0 := by
  have hEq : S.indicator M =ᵐ[P] M := by
    filter_upwards [hZeroOutside] with ω hZero
    by_cases hω : ω ∈ S
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω, hZero hω]
  calc
    (∫ ω in S, M ω ∂P) = (∫ ω, S.indicator M ω ∂P) :=
      (integral_indicator hS).symm
    _ = (∫ ω, M ω ∂P) := integral_congr_ae hEq
    _ = 0 := hMean
