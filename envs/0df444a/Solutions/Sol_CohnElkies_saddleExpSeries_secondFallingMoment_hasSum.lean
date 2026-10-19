-- Prove2me | solution 1 for CohnElkies.saddleExpSeries_secondFallingMoment_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/b982a459-2a0a-4d6a-b7f7-96396de0d95b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleExpSeries_hasSum

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution (y : ℝ) :
    HasSum
      (fun n : ℕ =>
        (n : ℝ) * ((n : ℝ) - 1) *
          (y ^ n / (n.factorial : ℝ)))
      (y ^ 2 * Real.exp y) := by
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) * ((n : ℝ) - 1) *
      (y ^ n / (n.factorial : ℝ))
  have hshift :
      (fun n : ℕ => f (n + 2)) =
      (fun n : ℕ => y ^ 2 *
        (y ^ n / (n.factorial : ℝ))) := by
    funext n
    try dsimp [f]
    rw [show n + 2 = (n + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ,
      pow_succ, pow_succ]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn' : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    have hfact : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp; ring
  have htail : HasSum (fun n : ℕ => f (n + 2))
      (y ^ 2 * Real.exp y) := by
    rw [hshift]
    exact (saddleExpSeries_hasSum y).mul_left (y ^ 2)
  have hfull := htail.sum_range_add
  simpa [f, Finset.sum_range_succ] using! hfull
end CohnElkies
