-- Prove2me | solution 2 for CohnElkies.upperGammaTruncatedDampingIntegrand_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:48.873776+00:00
-- url     : https://prove2.me/submissions/f66f4c24-fcc2-4ead-a07f-4030d45d34fe

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaTruncatedDampingIntegrand ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCosLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by
  unfold upperGammaTruncatedDampingIntegrand upperCosLaplaceKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Real.exp_nat_mul]
  have h : Real.exp (-(η + 2 * (k:ℝ) / ℓ) * a) = Real.exp (-η * a) * Real.exp (↑k * -(2 * a / ℓ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h]; ring

