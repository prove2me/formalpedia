-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_ball_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:51.396905+00:00
-- url     : https://prove2.me/submissions/482dc6e6-349c-440d-89f3-414d9ad1b17b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_As_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_ball_iff

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
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ball ϖ e (0 : Pts O A → ℤ) ↔ (coord e v : A) ∈ As O A := by
  rw [mem_ball_iff _ h he, mem_As_iff h]
  simp [ordV]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
