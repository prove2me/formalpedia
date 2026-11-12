-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva50_original_physical_u_grid_finite_jump_cell_isolation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:34:45.973794+00:00
-- url     : https://prove2.me/submissions/80bb71a8-6759-498d-8f20-f308586bc305

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva49_original_uniform_grid_isolates_finite_jump_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- The original physical uniform grid eventually has at most one mark per cell. -/
theorem solution (S : Finset ℝ) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, ∀ s t : ℝ,
      s ∈ S → t ∈ S →
      (u n i : ℝ) ≤ s → s < (u n (i + 1) : ℝ) →
      (u n i : ℝ) ≤ t → t < (u n (i + 1) : ℝ) → s = t := by
  have hcells := avram_bva49_original_uniform_grid_isolates_finite_jump_times S T hT
  filter_upwards [hcells] with n hn
  intro i s t hs ht hsi hsr hti htr
  have hstep : (u n (i + 1) : ℝ) =
      (u n i : ℝ) + T / ((n : ℝ) + 2) := by
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  rw [hstep] at hsr htr
  exact hn (u n i) s t hs ht hsi hsr hti htr
