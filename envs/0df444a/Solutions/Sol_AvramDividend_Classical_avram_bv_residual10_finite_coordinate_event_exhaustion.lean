-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_finite_coordinate_event_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:08:17.204851+00:00
-- url     : https://prove2.me/submissions/94ecbb7a-8b12-4f10-beb3-fd8c8645b1d8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- For a fixed finite original physical-grid row, the coefficient-bound
events exhaust every sample path as the clipping cutoff grows. -/
theorem solution
    {Ω : Type*} (n : ℕ) (a : Ω → ℕ → ℝ) (ω : Ω) :
    ∃ N : ℕ, ∀ k ≥ N,
      ω ∈ {z : Ω | ∀ i ∈ Finset.range (n + 1), abs (a z i) ≤ (k : ℝ)} := by
  classical
  let N : ℕ → ℕ := fun i => Classical.choose (exists_nat_gt (abs (a ω i)))
  have hN (i : ℕ) : abs (a ω i) < (N i : ℝ) := by
    exact Classical.choose_spec (exists_nat_gt (abs (a ω i)))
  let Nmax : ℕ := (Finset.range (n + 1)).sup N
  refine ⟨Nmax, ?_⟩
  intro k hk i hi
  have hsmall : N i ≤ Nmax := Finset.le_sup hi
  have hle : (N i : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (le_trans hsmall hk)
  exact (le_of_lt (hN i)).trans hle
