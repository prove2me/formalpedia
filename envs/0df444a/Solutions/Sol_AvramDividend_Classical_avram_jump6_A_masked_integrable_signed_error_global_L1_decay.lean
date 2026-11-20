-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_masked_integrable_signed_error_global_L1_decay
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:34:31.49259+00:00
-- url     : https://prove2.me/submissions/3efc14fd-a055-4be8-a4ea-a123f4bc42dd

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (B : Set Ω) (hB : MeasurableSet B)
    (Err : ℕ → Ω → ℝ) (hEI : ∀ k, Integrable (Err k) P)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖Err m ω‖ ∂P) ≤ ε) :
    (∀ k, Integrable (B.indicator (Err k)) P) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        (∫ ω, ‖(B.indicator (Err m)) ω‖ ∂P) ≤ ε) := by
  have hI : ∀ m, Integrable (B.indicator (Err m)) P :=
    fun m => (hEI m).indicator hB
  refine ⟨hI, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := hSmall ε hε
  refine ⟨N, ?_⟩
  intro m hm
  have hbound :
      (∫ ω, ‖(B.indicator (Err m)) ω‖ ∂P) ≤
        (∫ ω, ‖Err m ω‖ ∂P) := by
    apply integral_mono (hI m).norm (hEI m).norm
    intro ω
    by_cases hω : ω ∈ B
    · simp [Set.indicator, hω]
    · simp [Set.indicator, hω]
  exact hbound.trans (hN m hm)