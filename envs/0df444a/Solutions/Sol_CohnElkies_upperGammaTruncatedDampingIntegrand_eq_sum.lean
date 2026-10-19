-- Prove2me | solution 1 for CohnElkies.upperGammaTruncatedDampingIntegrand_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/8fb1b53d-7020-431c-abc2-939be696edca

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
namespace CohnElkies
theorem _root_.solution
    (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaTruncatedDampingIntegrand ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCosLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by
  classical
  unfold upperGammaTruncatedDampingIntegrand
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he :
      Real.exp (-η * a) *
          Real.exp (-(2 * a / ℓ)) ^ k =
        Real.exp (-(η + 2 * (k : ℝ) / ℓ) * a) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  unfold upperCosLaplaceKernel
  calc
    ((1 - Real.cos (a * T)) * Real.exp (-η * a) / a) *
        Real.exp (-(2 * a / ℓ)) ^ k =
      (1 - Real.cos (a * T)) *
        (Real.exp (-η * a) *
          Real.exp (-(2 * a / ℓ)) ^ k) / a := by
          ring
    _ = (1 - Real.cos (a * T)) *
        Real.exp (-(η + 2 * (k : ℝ) / ℓ) * a) / a := by
          rw [he]
end CohnElkies
