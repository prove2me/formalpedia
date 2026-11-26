-- Prove2me | solution 1 for Eden.innerRadialRegion_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:28.351881+00:00
-- url     : https://prove2.me/submissions/9104d8ef-b180-491e-9e4a-e82569d894c7

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution : innerRadialRegion.Nonempty := by
  refine ⟨0, ?_⟩
  norm_num [innerRadialRegion, attractor, radiusSq₁, radiusSq₂]
end Eden
