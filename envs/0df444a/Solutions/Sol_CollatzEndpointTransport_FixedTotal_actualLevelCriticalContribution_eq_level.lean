-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelCriticalContribution_eq_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:30:03.557243+00:00
-- url     : https://prove2.me/submissions/6744b3d6-bfd4-49e8-afa8-8ccfc28b2255

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelFiberCard_eq_levelEndpointFiberCard
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelSourceCard_eq_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelEndpointSet_eq_levelEndpointSet

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} (hs : 0 < s) :
    actualLevelCriticalContribution M s =
      levelCriticalContribution M s := by
  rw [actualLevelCriticalContribution, levelCriticalContribution,
    levelCriticalNumerator]
  rw [actualLevelEndpointSet_eq_levelEndpointSet hs]
  simp_rw [actualLevelFiberCard_eq_levelEndpointFiberCard hs]
  rw [← levelSourceCard_eq_card_sourceOddLevel hs]
end CollatzEndpointTransport.FixedTotal
