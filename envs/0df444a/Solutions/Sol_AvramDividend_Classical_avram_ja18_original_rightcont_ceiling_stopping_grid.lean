-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_rightcont_ceiling_stopping_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:06:12.520316+00:00
-- url     : https://prove2.me/submissions/a022e339-1b83-4092-9e70-cce071ba7db4

import Mathlib.Data.Nat.Find
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- The least covering grid index has exactly the stopping level events
of the original right-continuous clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, τ ω ≤ e N) :
    ∃ K : Ω → ℕ,
      (∀ ω, K ω ≤ N) ∧
      (∀ ω, τ ω ≤ e (K ω)) ∧
      (∀ i : ℕ,
        MeasurableSet[𝓕.rightCont (e i)] {ω | K ω ≤ i}) := by
  classical
  let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j :=
    fun ω => ⟨N, hN ω⟩
  let K : Ω → ℕ := fun ω =>
    @Nat.find (fun j : ℕ => τ ω ≤ e j)
      (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
  have hKiff (ω : Ω) (i : ℕ) :
      K ω ≤ i ↔ τ ω ≤ e i := by
    constructor
    · intro hi
      exact (Nat.find_spec (cover ω)).trans (he hi)
    · intro hi
      exact (Nat.find_le_iff (cover ω) i).2 ⟨i, le_rfl, hi⟩
  refine ⟨K, ?_, ?_, ?_⟩
  · intro ω
    exact (hKiff ω N).2 (hN ω)
  · intro ω
    exact Nat.find_spec (cover ω)
  · intro i
    have hs : {ω : Ω | K ω ≤ i} = {ω : Ω | τ ω ≤ e i} := by
      ext ω
      exact hKiff ω i
    rw [hs]
    simpa only [WithTop.coe_le_coe] using hτ (e i)
