-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a28_lindeberg_finite_mesh_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:49:22.171209+00:00
-- url     : https://prove2.me/submissions/29126dd6-2007-4e7e-b4e3-409c66ee9c28

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open BigOperators

/-- Sum the large-increment fourth-energy bound across the physical mesh. -/
theorem solution {ι : Type*} (s : Finset ι) (r : ℝ) (hr : 0 < r)
    (z : ι → ℝ) :
    (∑ i ∈ s, if r ≤ |z i| then (z i) ^ 2 else 0) ≤
      (∑ i ∈ s, (z i) ^ 4) / r ^ 2 := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact AvramDividend.Classical.avram_ga_a27_lindeberg_scalar_fourth_energy
    r (z i) hr
