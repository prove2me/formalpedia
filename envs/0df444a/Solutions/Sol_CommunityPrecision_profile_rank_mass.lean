-- Prove2me | solution 1 for CommunityPrecision.profile_rank_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/56d0af62-5f56-4e1b-a5ea-ef18fa3e9ae5

import Std
import Definitions.Def_CommunityPrecisionProfile

set_option autoImplicit true
open CommunityPrecision
namespace CommunityPrecision
theorem _root_.solution : rankMass profile = 421548223824 := by decide
end CommunityPrecision
