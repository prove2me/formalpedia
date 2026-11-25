-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordZ_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:15:13.244628+00:00
-- url     : https://prove2.me/submissions/53016449-0688-4c0a-af57-5ecd142f7a43

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coe_ordZ

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
theorem _root_.solution (h : IsUnif A ϖ) {x y : A} (hx : x ∈ nonZeroDivisors A)
    (hy : y ∈ nonZeroDivisors A) : ordZ ϖ ζ (x * y) = ordZ ϖ ζ x + ordZ ϖ ζ y := by
  apply WithTop.coe_injective
  rw [WithTop.coe_add, coe_ordZ ζ h hx, coe_ordZ ζ h hy, coe_ordZ ζ h (mul_mem hx hy),
    ord_mul ζ h]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
