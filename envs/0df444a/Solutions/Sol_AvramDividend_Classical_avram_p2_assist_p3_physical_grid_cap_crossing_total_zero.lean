-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_physical_grid_cap_crossing_total_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:49:02.984242+00:00
-- url     : https://prove2.me/submissions/f8304d58-8243-4572-958e-a7917931b351

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_self_cap_crossing_correction_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped ENNReal BigOperators
noncomputable section

/-- The exact cap-crossing correction in each stopped source mesh sums to zero. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (n : ℕ) (p : ℕ → ℝ) (e : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, e i *
      (if C = ⊤ then 0
       else if p i ≤ C.toReal then 0
       else V C.toReal + (p i - C.toReal) - V (p i))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [avram_p2_assist_p3_self_cap_crossing_correction_zero
    C w V hVtop hVfinite (p i)]
  ring
