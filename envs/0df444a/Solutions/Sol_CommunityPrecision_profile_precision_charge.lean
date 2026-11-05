-- Prove2me | solution 1 for CommunityPrecision.profile_precision_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/d1edd5db-b4e5-48e8-a82a-2087478ab587

import Std
import Definitions.Def_CommunityPrecisionProfile

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution : precisionCharge profile 1 = 211345564248 := by decide
end CommunityPrecision
