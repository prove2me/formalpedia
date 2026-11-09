-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_past_event_integral_of_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:24:07.310768+00:00
-- url     : https://prove2.me/submissions/63abc669-e8d3-4b2e-b11b-ccfc2425815e

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (M : Ω → ℝ) (hMI : Integrable M P)
    (hMzero : P[M | m] =ᵐ[P] 0)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    (∫ ω in A, M ω ∂P) = 0 := by
  classical
  calc
    (∫ ω in A, M ω ∂P) =
        (∫ ω in A, condExp m P M ω ∂P) :=
      (setIntegral_condExp hm hMI hA).symm
    _ = (∫ ω in A, (0 : ℝ) ∂P) := by
      exact integral_congr_ae (ae_restrict_of_ae hMzero)
    _ = 0 := by simp
