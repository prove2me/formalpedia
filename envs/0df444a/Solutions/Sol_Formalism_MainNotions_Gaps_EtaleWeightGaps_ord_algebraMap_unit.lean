-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_algebraMap_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:04.115431+00:00
-- url     : https://prove2.me/submissions/c61e4970-1191-402b-ad6f-65228443a1a8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq_zero_of_isUnit

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
variable {ϖ : O}
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (u : Oˣ) :
    ord ϖ ζ (algebraMap O A u) = 0 :=
  ord_eq_zero_of_isUnit ζ h (a := algebraMap O ↥(As O A) u) (u.isUnit.map _)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
