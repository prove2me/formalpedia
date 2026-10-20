-- Prove2me | solution 2 for CohnElkies.sharpAsymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:31:59.895328+00:00
-- url     : https://prove2.me/submissions/14ed739a-0e30-45f8-b284-a9a8476267ee

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpAsymptotics_of_signRadius_and_ordered_upper
import Theorems.Thm_CohnElkies_uniformAntiFourierSignRadius
import Theorems.Thm_CohnElkies_saddleSourceEventualSigns
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology


theorem solution :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic := by
  exact CohnElkies.sharpAsymptotics_of_signRadius_and_ordered_upper CohnElkies.uniformAntiFourierSignRadius
    (saddleOrderedUpperConstruction saddleSourceSchwartzRealization CohnElkies.saddleSourceEventualSigns)

