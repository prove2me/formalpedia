-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_right_mesh_cell_endpoint_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:35:02.284804+00:00
-- url     : https://prove2.me/submissions/beed7f0f-f991-45d4-b298-ade4306c240b

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped Classical

/-- On each half-open rational time cell, the right-hand ceiling endpoint
equals the cell's fixed right boundary, including the closed right endpoint. -/
theorem solution (n k : ℕ) (r : ℝ)
    (hr : r ∈ Ioc ((k : ℝ) / ((n : ℝ) + 1))
      (((k : ℝ) + 1) / ((n : ℝ) + 1))) :
    ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1) =
      ((k : ℝ) + 1) / ((n : ℝ) + 1) := by
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlo : (k : ℝ) < r * ((n : ℝ) + 1) :=
    (div_lt_iff₀ hp).mp hr.1
  have hhi : r * ((n : ℝ) + 1) ≤ (k : ℝ) + 1 :=
    (le_div_iff₀ hp).mp hr.2
  have hc : (⌈r * ((n : ℝ) + 1)⌉ : ℤ) = (k : ℤ) + 1 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · norm_num at *
      exact hlo
    · norm_num at *
      exact hhi
  rw [hc]
  norm_num
