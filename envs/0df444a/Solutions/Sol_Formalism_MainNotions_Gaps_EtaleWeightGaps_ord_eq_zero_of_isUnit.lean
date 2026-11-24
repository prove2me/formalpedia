-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_eq_zero_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:22.498736+00:00
-- url     : https://prove2.me/submissions/3c3f0d54-1a24-4e88-8da9-5ca95b4fcc06

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_zero_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_of_mem

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
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) {a : ↥(As O A)}
    (ha : IsUnit a) : ord ϖ ζ (a : A) = 0 := by
  rw [ord_of_mem ζ h a.2]
  have h1 : vL ζ a = 0 := by
    rw [vL_eq_zero_iff]
    exact fun hm => ζ.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hm ha)
  change (vL ζ a).map (Nat.cast : ℕ → ℤ) = 0
  rw [h1]
  rfl
end Formalism.MainNotions.Gaps.EtaleWeightGaps
