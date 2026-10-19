-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/bb1013af-a214-4426-a0a7-7ae65a0d499f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (n : ℕ) (x : ℝ) :
    iteratedDeriv n upperImaginaryExp x =
      Complex.I ^ n * upperImaginaryExp x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv n upperImaginaryExp =
            fun t : ℝ => Complex.I ^ n * upperImaginaryExp t := by
        funext t
        exact ih t
      rw [heq]
      have hderiv :=
        (upperImaginaryExp_hasDerivAt x).const_mul
          (Complex.I ^ n)
      rw [hderiv.deriv]
      rw [pow_succ]
      ring
end CohnElkies
