-- Prove2me | solution 1 for CommunityPrecision.profile_saving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/2b50520a-1609-43df-a276-697df9c0826c

import Std
import Definitions.Def_CommunityPrecisionProfile
import Theorems.Thm_CommunityPrecision_profile_rank_mass
import Theorems.Thm_CommunityPrecision_profile_precision_charge

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution : rankMass profile - precisionCharge profile 1 = 210202659576 := by
  rw [profile_rank_mass, profile_precision_charge]
end CommunityPrecision
