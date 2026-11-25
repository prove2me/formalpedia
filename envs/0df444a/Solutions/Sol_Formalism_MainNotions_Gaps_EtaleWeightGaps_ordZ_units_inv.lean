-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordZ_units_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:57.955284+00:00
-- url     : https://prove2.me/submissions/30d40ddd-5cda-455e-8d48-74f1e0494c40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_units_add_inv
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
theorem _root_.solution (h : IsUnif A ϖ) (u : Aˣ) :
    ordZ ϖ ζ ((u⁻¹ : Aˣ) : A) = - ordZ ϖ ζ (u : A) := by
  have h1 := ord_units_add_inv ζ h u
  rw [← coe_ordZ ζ h u.isUnit.mem_nonZeroDivisors,
    ← coe_ordZ ζ h (u⁻¹).isUnit.mem_nonZeroDivisors, ← WithTop.coe_add, ← WithTop.coe_zero,
    WithTop.coe_inj] at h1
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps
