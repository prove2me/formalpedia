-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:33.737195+00:00
-- url     : https://prove2.me/submissions/8886d4a6-b1dd-4c0b-b2ab-fb2f37926a9d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_unif
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow

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
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (k : ℕ) (x : A) :
    ord ϖ ζ (ϖ ^ k • x) = (((k : ℤ) * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) + ord ϖ ζ x := by
  rw [Algebra.smul_def, map_pow, ord_mul ζ h, ord_pow ζ h, ord_unif ζ h]
  rw [← WithTop.coe_nsmul, nsmul_eq_mul]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
