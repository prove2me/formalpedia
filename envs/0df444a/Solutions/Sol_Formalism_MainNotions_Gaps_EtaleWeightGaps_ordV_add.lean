-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:12.743884+00:00
-- url     : https://prove2.me/submissions/c1aecf61-eb6c-4f6a-beaf-ac810003ec88

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_add
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_add

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
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (v w : V) :
    min (ordV ϖ ζ e c v) (ordV ϖ ζ e c w) ≤ ordV ϖ ζ e c (v + w) := by
  rw [ordV, ordV, ordV, coord_add he, min_add_add_right]
  exact add_le_add_left (ord_add ζ h _ _) _
end Formalism.MainNotions.Gaps.EtaleWeightGaps
