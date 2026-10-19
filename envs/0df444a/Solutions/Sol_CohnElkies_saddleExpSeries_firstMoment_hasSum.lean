-- Prove2me | solution 1 for CohnElkies.saddleExpSeries_firstMoment_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/7e869b17-0637-496f-9fbc-7496c557e54a

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
      (fun n : ℕ => (n : ℝ) *
        (y ^ n / (n.factorial : ℝ)))
      (y * Real.exp y) := by
  let f : ℕ → ℝ := fun n =>
    (n : ℝ) * (y ^ n / (n.factorial : ℝ))
  have hshift :
      (fun n : ℕ => f (n + 1)) =
      (fun n : ℕ => y *
        (y ^ n / (n.factorial : ℝ))) := by
    funext n
    try dsimp [f]
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hfact : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp
  have htail : HasSum (fun n : ℕ => f (n + 1))
      (y * Real.exp y) := by
    rw [hshift]
    exact (saddleExpSeries_hasSum y).mul_left y
  simpa [f] using! htail.zero_add
end CohnElkies
