-- Prove2me | solution 1 for CommunityPrecision.arbitrary_profile_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/dc959814-db50-4def-88d6-bc6b68106f9c

import Std
import Definitions.Def_CommunityPrecisionProfile
import Theorems.Thm_CommunityPrecision_ceilHalf_mul_bound

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution (xs : List (Nat × Nat)) (f : Nat) :
    precisionCharge xs f ≤ precisionCharge xs 1 * f := by
  induction xs with
  | nil => simp [precisionCharge]
  | cons x xs ih =>
    simp only [precisionCharge, List.map_cons, List.sum_cons] at *
    rw [Nat.add_mul]
    have h := Nat.mul_le_mul_right x.2 (ceilHalf_mul_bound x.1 f)
    simpa only [Nat.mul_one, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      using Nat.add_le_add h ih
end CommunityPrecision
