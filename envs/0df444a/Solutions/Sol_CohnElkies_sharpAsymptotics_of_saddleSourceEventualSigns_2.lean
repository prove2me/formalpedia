-- Prove2me | solution 2 for CohnElkies.sharpAsymptotics_of_saddleSourceEventualSigns
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:31:50.016719+00:00
-- url     : https://prove2.me/submissions/ad160287-fb5b-4bb0-b61c-f86d5e472a6b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpAsymptotics_of_signRadius_and_ordered_upper
import Theorems.Thm_CohnElkies_uniformAntiFourierSignRadius
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution
    (hsigns : SaddleSourceEventualSigns) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic := by
  exact CohnElkies.sharpAsymptotics_of_signRadius_and_ordered_upper CohnElkies.uniformAntiFourierSignRadius
    (saddleOrderedUpperConstruction saddleSourceSchwartzRealization hsigns)

