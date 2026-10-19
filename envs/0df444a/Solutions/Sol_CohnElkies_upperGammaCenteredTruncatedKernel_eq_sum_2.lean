-- Prove2me | solution 2 for CohnElkies.upperGammaCenteredTruncatedKernel_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:06.52435+00:00
-- url     : https://prove2.me/submissions/31f648dd-8123-465e-8083-14b8cf491ae4

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
    upperGammaCenteredTruncatedKernel ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCenteredLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by
  unfold upperGammaCenteredTruncatedKernel upperCenteredLaplaceKernel
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc]
  congr 1
  push_cast
  rw [← Complex.exp_nat_mul, div_mul_eq_mul_div, ← Complex.exp_add]
  congr 2
  ring

