-- Prove2me | solution 1 for CohnElkies.lowerWallis_arg_one_sub_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/fcbc29a1-5d25-4949-9338-5bc285100154

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    Complex.arg (1 - Complex.I * (u : ℂ)) =
      -Real.arctan u := by
  let z : ℂ := 1 - Complex.I * (u : ℂ)
  have hre : 0 < z.re := by
    try dsimp [z]
    simp
  have hrange : |Complex.arg z| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have htan : Real.tan (Complex.arg z) = -u := by
    simp [z]
  calc
    Complex.arg (1 - Complex.I * (u : ℂ)) =
        Real.arctan (Real.tan (Complex.arg z)) := by
      change Complex.arg z =
        Real.arctan (Real.tan (Complex.arg z))
      exact (Real.arctan_tan
        (abs_lt.mp hrange).1 (abs_lt.mp hrange).2).symm
    _ = Real.arctan (-u) := by rw [htan]
    _ = -Real.arctan u := Real.arctan_neg u
end CohnElkies
