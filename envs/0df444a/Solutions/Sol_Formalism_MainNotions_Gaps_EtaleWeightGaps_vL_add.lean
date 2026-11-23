-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.vL_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:58.109856+00:00
-- url     : https://prove2.me/submissions/91fb5fb9-5f21-4a51-9328-1d9c5ed92d3b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_addVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
variable {O A}
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
variable (ζ : Pts O A) [IsDVRAt ζ]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (a b : ↥(As O A)) : min (vL ζ a) (vL ζ b) ≤ vL ζ (a + b) := by
  simp only [vL_eq_addVal, map_add]
  exact IsDiscreteValuationRing.addVal_add
end Formalism.MainNotions.Gaps.EtaleWeightGaps
