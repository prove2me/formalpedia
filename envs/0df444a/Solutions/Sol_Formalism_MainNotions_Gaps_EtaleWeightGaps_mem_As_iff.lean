-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_As_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:31.407169+00:00
-- url     : https://prove2.me/submissions/1ce0dac9-94bd-4530-9f97-b22293c3504c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_addVal
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_nonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_nonneg_iff

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
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (x : A) :
    x ∈ As O A ↔ ∀ ζ : Pts O A, 0 ≤ ord ϖ ζ x := by
  refine ⟨fun hx ζ => ord_nonneg ζ h hx, fun hx => ?_⟩
  obtain ⟨n, hn⟩ := h.denom x
  have key : (⟨ϖ ^ n • x, hn⟩ : ↥(As O A)) ∈ Ideal.span {(algebraMap O ↥(As O A) ϖ) ^ n} := by
    have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) ⟨ϖ ^ n • x, hn⟩ ∈
        Ideal.map (algebraMap ↥(As O A) (Loc ζ))
          (Ideal.span {(algebraMap O ↥(As O A) ϖ) ^ n}) := by
      intro ζ
      have h1 := hx ζ
      rw [ord_eq ζ h hn, ordAt_nonneg_iff ζ h, vL_eq_addVal, vL_eq_addVal,
        IsDiscreteValuationRing.addVal_le_iff_dvd] at h1
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact h1
    exact Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 key
  have h2 : (algebraMap O A ϖ) ^ n * x = (algebraMap O A ϖ) ^ n * (b : A) := by
    have := congrArg Subtype.val hb
    simpa [Algebra.smul_def] using this
  rw [(h.isUnit.pow n).mul_right_inj.1 h2]
  exact b.2
end Formalism.MainNotions.Gaps.EtaleWeightGaps
