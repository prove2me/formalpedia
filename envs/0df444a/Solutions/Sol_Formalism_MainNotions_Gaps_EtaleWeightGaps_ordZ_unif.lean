-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordZ_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:15:18.657205+00:00
-- url     : https://prove2.me/submissions/346caf39-9f5a-4fe1-b352-7686965a9aff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_unif

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
theorem _root_.solution (h : IsUnif A ϖ) : ordZ ϖ ζ (algebraMap O A ϖ) = ep ϖ ζ := by
  rw [ordZ, ord_unif ζ h]
  rfl
end Formalism.MainNotions.Gaps.EtaleWeightGaps
