-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:53.811927+00:00
-- url     : https://prove2.me/submissions/a8be867d-e36d-401a-a925-3921114716bf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_shift

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
theorem _root_.solution (h : IsUnif A ϖ) {x : A} {n m : ℕ} (hn : ϖ ^ n • x ∈ As O A)
    (hm : ϖ ^ m • x ∈ As O A) :
    ordAt ϖ ζ n ⟨ϖ ^ n • x, hn⟩ = ordAt ϖ ζ m ⟨ϖ ^ m • x, hm⟩ := by
  rw [← ordAt_shift ζ h n m ⟨ϖ ^ n • x, hn⟩, ← ordAt_shift ζ h m n ⟨ϖ ^ m • x, hm⟩, add_comm m n]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Algebra.smul_def, map_pow]
  have : ((algebraMap O ↥(As O A) ϖ : ↥(As O A)) : A) = algebraMap O A ϖ := rfl
  rw [this]
  ring
end Formalism.MainNotions.Gaps.EtaleWeightGaps
