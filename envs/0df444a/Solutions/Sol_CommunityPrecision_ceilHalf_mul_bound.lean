-- Prove2me | solution 1 for CommunityPrecision.ceilHalf_mul_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/d71a7b3d-69bb-45dd-a0fd-a2430689ba00

import Std
import Definitions.Def_CommunityPrecisionProfile
import Theorems.Thm_CommunityPrecision_ceilHalf_subadditive

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution (r f : Nat) :
    ceilHalf (r*f) ≤ ceilHalf r * f := by
  induction f with
  | zero => simp [ceilHalf]
  | succ f ih =>
    rw [Nat.mul_succ, Nat.mul_succ]
    exact Nat.le_trans (ceilHalf_subadditive _ _) (Nat.add_le_add_right ih _)
end CommunityPrecision
