-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coe_ordZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:31.285204+00:00
-- url     : https://prove2.me/submissions/ec8b515e-fb65-4ecb-8406-0b77175f6319

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_ne_top

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
theorem _root_.solution (h : IsUnif A ϖ) {x : A} (hx : x ∈ nonZeroDivisors A) :
    ((ordZ ϖ ζ x : ℤ) : WithTop ℤ) = ord ϖ ζ x := by
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 (ord_ne_top ζ h hx)
  rw [ordZ, ← hz]
  rfl
end Formalism.MainNotions.Gaps.EtaleWeightGaps
