-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.pow_smul_coord_mem_As
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:14.333377+00:00
-- url     : https://prove2.me/submissions/ae65ca3d-584f-434a-aed5-94e1c3f1c6c6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow_smul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_As_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_ball_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_le_mul_ep

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
variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {N : ℕ} (hc : ∀ ζ, c ζ ≤ (N : ℤ)) {v : V} (hv : v ∈ ball ϖ e c) :
    ϖ ^ N • (coord e v : A) ∈ As O A := by
  rw [mem_ball_iff c h he] at hv
  rw [mem_As_iff h]
  intro ζ
  rw [ord_pow_smul ζ h, add_comm]
  refine (hv ζ).trans (add_le_add_right (WithTop.coe_le_coe.2 ?_) _)
  exact (hc ζ).trans (le_mul_ep ζ h N)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
