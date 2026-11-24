-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_units_add_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:06.8548+00:00
-- url     : https://prove2.me/submissions/c4058388-8ece-4e24-817f-debbf1d821fc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_one
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul

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
variable {ϖ : O} (ζ : Pts O A) [IsDVRAt ζ]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (h : IsUnif A ϖ) (u : Aˣ) :
    ord ϖ ζ (u : A) + ord ϖ ζ ((u⁻¹ : Aˣ) : A) = 0 := by
  rw [← ord_mul ζ h, Units.mul_inv, ord_one ζ h]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
