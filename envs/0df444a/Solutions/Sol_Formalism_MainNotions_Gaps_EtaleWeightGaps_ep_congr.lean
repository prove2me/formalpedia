-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ep_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:40.606319+00:00
-- url     : https://prove2.me/submissions/56104755-1ac8-438f-9089-2620faa921fe

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ep_eq_ramificationIdx

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
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution {ϖ ϖ' : O} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (ζ : Pts O A) :
    ep ϖ ζ = ep ϖ' ζ := by
  rw [ep_eq_ramificationIdx hϖ, ep_eq_ramificationIdx hϖ']
end Formalism.MainNotions.Gaps.EtaleWeightGaps
