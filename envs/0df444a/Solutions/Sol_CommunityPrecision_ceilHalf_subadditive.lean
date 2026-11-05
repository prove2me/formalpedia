-- Prove2me | solution 1 for CommunityPrecision.ceilHalf_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/171ee989-04f9-4beb-af1c-bc671a46a48a

import Std
import Definitions.Def_CommunityPrecisionProfile

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution (a b : Nat) :
    ceilHalf (a+b) ≤ ceilHalf a + ceilHalf b := by
  unfold ceilHalf
  omega
end CommunityPrecision
