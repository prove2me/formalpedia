-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_event_independent_surrogate_gain_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:16:32.663336+00:00
-- url     : https://prove2.me/submissions/1b716191-3d8d-48e9-8147-e5cb86511ce4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (A : Set Ω) (hA : MeasurableSet[m] A)
    (G H : ℕ → Ω → ℝ)
    (hHI : ∀ n, Integrable (H n) P)
    (hInd : ∀ n,
      ProbabilityTheory.Indep m
        (MeasurableSpace.comap (H n) inferInstance) P)
    (hSame : ∀ n, ∀ᵐ ω ∂(P.restrict A), G n ω = H n ω)
    (hZero : ∀ n, (∫ ω, H n ω ∂P) = 0) :
    ∀ n, (∫ ω in A, G n ω ∂P) = 0 := by
  intro n
  have hEqInt :
      (∫ ω in A, G n ω ∂P) =
        (∫ ω in A, H n ω ∂P) := integral_congr_ae (hSame n)
  have hIndInt :
      (∫ ω in A, H n ω ∂P) =
        P.real A * (∫ ω, H n ω ∂P) := by
    simpa only [Function.comp_id, id_eq] using
      (ProbabilityTheory.Indep.setIntegral_eq_mul
        (X := H n) (f := id) hm (hInd n)
        (hHI n).aemeasurable hA measurable_id.aestronglyMeasurable)
  rw [hEqInt, hIndInt, hZero n, mul_zero]
