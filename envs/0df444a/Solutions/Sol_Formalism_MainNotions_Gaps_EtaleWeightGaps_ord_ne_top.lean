-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:31:43.377747+00:00
-- url     : https://prove2.me/submissions/9415e0f3-9615-469d-82f7-ea84f706e227

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_ne_top
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq

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
theorem _root_.solution (h : IsUnif A ϖ) {x : A} (hx : x ∈ nonZeroDivisors A) : ord ϖ ζ x ≠ ⊤ := by
  obtain ⟨n, hn⟩ := h.denom x
  rw [ord_eq ζ h hn, ordAt]
  have h1 : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) ∈ nonZeroDivisors ↥(As O A) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    have h2 : (b : A) * (ϖ ^ n • x) = 0 := congrArg Subtype.val hb
    rw [Algebra.smul_def, map_pow, mul_left_comm] at h2
    have h3 := ((h.isUnit.pow n).mul_right_eq_zero).1 h2
    exact Subtype.ext ((mem_nonZeroDivisors_iff_right.1 hx) _ h3)
  have h2 := vL_ne_top ζ h1
  rw [Ne, WithTop.add_eq_top, not_or]
  exact ⟨by simpa using h2, WithTop.coe_ne_top⟩
end Formalism.MainNotions.Gaps.EtaleWeightGaps
