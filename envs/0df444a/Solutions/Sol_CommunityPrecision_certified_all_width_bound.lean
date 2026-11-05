-- Prove2me | solution 1 for CommunityPrecision.certified_all_width_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/06e29705-969b-46ee-922a-deecea952469

import Std
import Definitions.Def_CommunityPrecisionProfile
import Theorems.Thm_CommunityPrecision_arbitrary_profile_bound
import Theorems.Thm_CommunityPrecision_profile_precision_charge

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution (f : Nat) :
    precisionCharge profile f ≤ 211345564248 * f := by
  simpa only [profile_precision_charge] using arbitrary_profile_bound profile f
end CommunityPrecision
