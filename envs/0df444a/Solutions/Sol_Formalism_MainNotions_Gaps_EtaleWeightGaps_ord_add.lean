-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:31:46.065224+00:00
-- url     : https://prove2.me/submissions/32ef0de2-5e4f-404d-a8f6-bf5a6b103a6d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_add

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
theorem _root_.solution (h : IsUnif A ϖ) (x y : A) :
    min (ord ϖ ζ x) (ord ϖ ζ y) ≤ ord ϖ ζ (x + y) := by
  obtain ⟨n, hn⟩ := h.denom x
  obtain ⟨m, hm⟩ := h.denom y
  have hx : ϖ ^ (n + m) • x ∈ As O A := by
    rw [add_comm, pow_add, mul_smul]; exact (As O A).smul_mem hn _
  have hy : ϖ ^ (n + m) • y ∈ As O A := by
    rw [pow_add, mul_smul]; exact (As O A).smul_mem hm _
  have hxy : ϖ ^ (n + m) • (x + y) ∈ As O A := by
    rw [smul_add]; exact (As O A).add_mem hx hy
  rw [ord_eq ζ h hx, ord_eq ζ h hy, ord_eq ζ h hxy]
  refine (ordAt_add ζ _ _ _).trans (le_of_eq ?_)
  congr 1
  exact Subtype.ext (smul_add _ _ _).symm
end Formalism.MainNotions.Gaps.EtaleWeightGaps
