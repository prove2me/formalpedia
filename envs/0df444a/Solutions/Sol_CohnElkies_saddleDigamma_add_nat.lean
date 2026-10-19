-- Prove2me | solution 1 for CohnElkies.saddleDigamma_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/1f82817d-1833-456a-bc7c-f1e42231f1dd

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleDigamma_add_one

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
    {m : ℝ} (hm : 0 < m) (n : ℕ) :
    saddleDigamma (m + (n : ℝ)) =
      saddleDigamma m +
        ∑ k ∈ Finset.range n,
          (m + (k : ℝ))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc,
      saddleDigamma_add_one (by positivity),
      ih, Finset.sum_range_succ]
    ring
end CohnElkies
