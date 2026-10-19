-- Prove2me | solution 1 for CohnElkies.sharpAsymptotics_of_saddleSourceEventualSigns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/2dd128d0-d904-4458-9cf4-aa662375d989

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_uniformAntiFourierSignRadius
import Theorems.Thm_CohnElkies_sharpAsymptotics_of_signRadius_and_ordered_upper

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (hsigns : SaddleSourceEventualSigns) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic :=
  sharpAsymptotics_of_signRadius_and_ordered_upper
    uniformAntiFourierSignRadius
    (saddleOrderedUpperConstruction_of_sourceSigns hsigns)
end CohnElkies
