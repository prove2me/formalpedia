-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:09.564203+00:00
-- url     : https://prove2.me/submissions/8adc3146-0d42-494c-a84f-2617e170ad26

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
variable {ϖ : O}
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (x : A) (k : ℕ) :
    ord ϖ ζ (x ^ k) = k • ord ϖ ζ x := by
  induction k with
  | zero => simp [ord_one ζ h]
  | succ k ih => rw [pow_succ, ord_mul ζ h, ih, succ_nsmul]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
