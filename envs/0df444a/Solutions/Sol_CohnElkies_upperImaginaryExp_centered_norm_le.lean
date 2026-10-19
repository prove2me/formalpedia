-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_centered_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/d6b949b8-7c88-45fa-8cba-a6babdfdc8a4

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_quadratic_remainder_norm_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (x : ℝ) :
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ)‖ ≤
      x ^ 2 / 2 + |x| ^ 3 / 6 := by
  let q : ℂ := ((x ^ 2 / 2 : ℝ) : ℂ)
  have hq : ‖q‖ = x ^ 2 / 2 := by
    try dsimp [q]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  calc
    ‖upperImaginaryExp x - 1 -
        Complex.I * (x : ℂ)‖ =
      ‖(upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) + q) - q‖ := by
        congr 1
        ring
    _ ≤ ‖upperImaginaryExp x - 1 -
          Complex.I * (x : ℂ) + q‖ + ‖q‖ :=
      norm_sub_le _ _
    _ ≤ |x| ^ 3 / 6 + x ^ 2 / 2 := by
      rw [hq]
      try dsimp [q]
      exact add_le_add
        (upperImaginaryExp_quadratic_remainder_norm_le x)
        (le_refl _)
    _ = x ^ 2 / 2 + |x| ^ 3 / 6 := by ring
end CohnElkies
