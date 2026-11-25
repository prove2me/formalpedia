-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:59.097606+00:00
-- url     : https://prove2.me/submissions/b48c0cce-aba2-4f05-9d08-b5612238cf1b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_one
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_gen

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
    ordV ϖ ζ e c e = ((c ζ : ℤ) : WithTop ℤ) := by
  rw [ordV, coord_gen he, ord_one ζ h, zero_add]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
