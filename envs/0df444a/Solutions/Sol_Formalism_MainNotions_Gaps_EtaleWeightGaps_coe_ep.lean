-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coe_ep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:12.192033+00:00
-- url     : https://prove2.me/submissions/3ce633fd-459c-4de5-93c1-19f111d9b5eb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_ne_top
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_unif_mem_nonZeroDivisors

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
variable (ζ : Pts O A) [IsDVRAt ζ]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (h : IsUnif A ϖ) : (ep ϖ ζ : ℕ∞) = vL ζ (algebraMap O ↥(As O A) ϖ) :=
  ENat.natCast_toNat (vL_ne_top ζ (unif_mem_nonZeroDivisors h))
end Formalism.MainNotions.Gaps.EtaleWeightGaps
