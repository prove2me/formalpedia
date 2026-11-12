-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger122_monotone_stopped_grid_postcrossing_plateau
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:48:43.818389+00:00
-- url     : https://prove2.me/submissions/ed018888-43d0-4b65-b226-c174eab9ac4a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

/-- A bounded monotone grid stays at the stop after its first crossing. -/
theorem solution
    (v : ℕ → ℝ≥0) (hv : Monotone v)
    (ρ : ℝ≥0) (hbound : ∀ i : ℕ, v i ≤ ρ)
    (k : ℕ) (hcross : v (k + 1) = ρ) :
    ∀ i : ℕ, k < i → v i = ρ ∧ v (i + 1) = ρ := by
  intro i hi
  have hki : k + 1 ≤ i := by omega
  have hρi : ρ ≤ v i := by simpa [hcross] using hv hki
  have hvi : v i = ρ := le_antisymm (hbound i) hρi
  have hnext : v (i + 1) = ρ := by
    apply le_antisymm (hbound (i + 1))
    calc
      ρ = v i := hvi.symm
      _ ≤ v (i + 1) := hv (Nat.le_succ i)
  exact ⟨hvi, hnext⟩
