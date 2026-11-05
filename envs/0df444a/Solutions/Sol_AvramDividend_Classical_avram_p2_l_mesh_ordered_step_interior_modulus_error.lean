-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_ordered_step_interior_modulus_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:45:37.082223+00:00
-- url     : https://prove2.me/submissions/6706f462-69a2-4e86-aed1-cbe45f884a10

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_strict_partition_cell_sum_eq_sample

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped BigOperators

/-- An ordered fine partition approximates a test uniformly on each cell. -/
theorem solution {n : ℕ} (f : ℝ → ℝ) (a b : Fin n → ℝ)
    (hordered : ∀ i j : Fin n, i < j → b i ≤ a j)
    (δ η : ℝ)
    (hmod : ∀ x y : ℝ, |x - y| < δ → |f x - f y| < η)
    (hwidth : ∀ i : Fin n, b i - a i < δ)
    (z : ℝ) (i : Fin n) (hi : z ∈ Ioc (a i) (b i)) :
    |f z - (∑ j : Fin n,
      if z ∈ Ioc (a j) (b j) then f (a j) else 0)| < η := by
  have hcell := avram_p2_l_mesh_strict_partition_cell_sum_eq_sample
    a b (fun j => f (a j)) hordered z i hi
  have hz : |z - a i| < δ := by
    rw [abs_of_pos (sub_pos.mpr hi.1)]
    have hcap := hi.2
    have hw := hwidth i
    linarith
  rw [hcell]
  exact hmod z (a i) hz
