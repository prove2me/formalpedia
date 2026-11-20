-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_integrable_error_global_L1_controls_initial_event_signed_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:16:24.794371+00:00
-- url     : https://prove2.me/submissions/fa71f6e2-4b2e-4783-a0e3-b3e10b64c50e

import Mathlib
open MeasureTheory Filter Set Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (hA : MeasurableSet A)
    (Err : ℕ → Ω → ℝ) (hEI : ∀ m, Integrable (Err m) P)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖Err m ω‖ ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, (∫ ω in A, Err m ω ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hSmall ε hε
  refine ⟨N, ?_⟩
  have hLeNorm :
      (∫ ω in A, Err N ω ∂P) ≤
        (∫ ω in A, ‖Err N ω‖ ∂P) := by
    apply integral_mono (hEI N).integrableOn (hEI N).norm.integrableOn
    intro ω
    exact le_abs_self (Err N ω)
  have hBoundNorm :
      (∫ ω in A, ‖Err N ω‖ ∂P) ≤
        (∫ ω, ‖Err N ω‖ ∂P) := by
    apply integral_mono_measure (Measure.restrict_le_self)
    · exact Filter.Eventually.of_forall (fun ω => norm_nonneg (Err N ω))
    · exact (hEI N).norm
  exact hLeNorm.trans (hBoundNorm.trans (hN N le_rfl))
