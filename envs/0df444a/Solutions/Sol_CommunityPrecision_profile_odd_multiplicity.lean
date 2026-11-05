-- Prove2me | solution 1 for CommunityPrecision.profile_odd_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/2b0f23ac-5ff7-4174-a449-0815553644e1

import Std
import Definitions.Def_CommunityPrecisionProfile

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution : oddMultiplicity profile = 1142904672 := by decide
end CommunityPrecision
