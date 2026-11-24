-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ball_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:16.169632+00:00
-- url     : https://prove2.me/submissions/9951ca08-0be7-4b01-be1d-66ba874ee950

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
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
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {c c' : Pts O A → ℤ} (hc : c ≤ c') : ball ϖ e c ≤ ball ϖ e c' := by
  intro v hv
  rw [mem_ball_iff _ h he] at hv ⊢
  exact fun ζ => (hv ζ).trans (add_le_add_right (WithTop.coe_le_coe.2 (hc ζ)) _)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
