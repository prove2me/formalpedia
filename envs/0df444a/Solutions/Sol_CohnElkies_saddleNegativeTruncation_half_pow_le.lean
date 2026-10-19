-- Prove2me | solution 1 for CohnElkies.saddleNegativeTruncation_half_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/441b2b8a-0fb2-48ce-b77f-1de8e09756f3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallResidueTruncation_half_pow_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution (ℓ : ℝ) :
    (1 / 2 : ℝ) ^ saddleSmallResidueTruncation ℓ ≤
      2 * Real.exp (-10 * Real.log ℓ) := by
  have hnext := saddleSmallResidueTruncation_half_pow_le ℓ
  calc
    (1 / 2 : ℝ) ^ saddleSmallResidueTruncation ℓ =
      2 * (1 / 2 : ℝ) ^
        (saddleSmallResidueTruncation ℓ + 1) := by
          rw [pow_succ]
          ring
    _ ≤ 2 * Real.exp (-10 * Real.log ℓ) :=
      mul_le_mul_of_nonneg_left hnext (by norm_num)
end CohnElkies
