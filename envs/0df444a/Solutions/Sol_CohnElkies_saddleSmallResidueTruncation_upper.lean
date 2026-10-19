-- Prove2me | solution 1 for CohnElkies.saddleSmallResidueTruncation_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/19d62a6f-f509-423c-9c75-8280847d9b84

import Mathlib
import Definitions.Def_SpherePacking

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
    {ℓ : ℝ} (hℓ : 1 ≤ ℓ) :
    (saddleSmallResidueTruncation ℓ : ℝ) ≤
      20 * Real.log ℓ + 1 := by
  exact (Nat.ceil_lt_add_one
    (mul_nonneg (by norm_num)
      (Real.log_nonneg hℓ))).le
end CohnElkies
