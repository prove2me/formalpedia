-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:12.225005+00:00
-- url     : https://prove2.me/submissions/cecee40d-e656-4e59-a6c3-b2e5b31ff8f8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_zero
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_zero

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
variable {V : Type*} [AddCommGroup V] [Module A V]
variable {ϖ : O} {e : V} (c : Pts O A → ℤ)
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) :
    ordV ϖ ζ e c 0 = ⊤ := by
  rw [ordV, coord_zero he, ord_zero ζ h, top_add]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
