-- Prove2me | solution 1 for AvramDividend.Classical.avram_b22_initial_event_finite_mesh_vanishing_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:30:49.102197+00:00
-- url     : https://prove2.me/submissions/40444cbf-1898-46bd-8723-46925e43b1e5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite ruin-clipped mesh needs only locally centred aggregate noise and arbitrarily small expected error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F : Ω → ℝ) (hFI : IntegrableOn F A P)
    (M Err : ℕ → Ω → ℝ)
    (hMI : ∀ n, IntegrableOn (M n) A P)
    (hEI : ∀ n, IntegrableOn (Err n) A P)
    (hMzero : ∀ n, (∫ ω in A, M n ω ∂P) = 0)
    (hBound : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ b + M n ω + Err n ω)
    (hErr : ∀ ε : ℝ, 0 < ε →
      ∃ n, (∫ ω in A, Err n ω ∂P) ≤ ε) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by
  classical
  by_contra hh
  have hGap : 0 < (∫ ω in A, F ω ∂P) - b * (P A).toReal := by
    have hStrict : b * (P A).toReal < (∫ ω in A, F ω ∂P) :=
      lt_of_not_ge hh
    linarith
  obtain ⟨n, hn⟩ := hErr _ (by linarith : 0 < ((∫ ω in A, F ω ∂P) - b * (P A).toReal) / 2)
  have hBudget :=
    avram_b21_initial_event_local_aggregate_budget
      A hA b F (M n) (Err n) hFI (hMI n) (hEI n) (hMzero n)
      (hBound n)
  linarith
