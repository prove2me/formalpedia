-- Prove2me | solution 1 for Eden.radialRegions_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:36.991233+00:00
-- url     : https://prove2.me/submissions/5f04401f-1b82-4627-90b9-852d7187b033

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution : Disjoint innerRadialRegion outerRadialRegion := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact (not_lt_of_ge hp.2.le) hq.2
end Eden
