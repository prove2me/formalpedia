-- Prove2me | solution 1 for CohnElkies.upperGammaCenteredTruncatedKernel_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/a6ad8131-411f-4201-81b7-7b52b58d6abc

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
    upperGammaCenteredTruncatedKernel ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1),
        upperCenteredLaplaceKernel
          (η + 2 * (k : ℝ) / ℓ) T a := by
  classical
  unfold upperGammaCenteredTruncatedKernel
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he :
      Complex.exp (-(η : ℂ) * (a : ℂ)) *
          Complex.exp (-(2 * (a : ℂ) / (ℓ : ℂ))) ^ k =
        Complex.exp
          (-((η : ℂ) + 2 * (k : ℂ) / (ℓ : ℂ)) *
            (a : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  unfold upperCenteredLaplaceKernel
  push_cast
  rw [← he]
  ring
end CohnElkies
