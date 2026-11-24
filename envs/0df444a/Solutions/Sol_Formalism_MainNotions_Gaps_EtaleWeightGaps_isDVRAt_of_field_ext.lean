-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.isDVRAt_of_field_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:22.014815+00:00
-- url     : https://prove2.me/submissions/a3b608dc-676b-4c98-80e2-739b98c47248

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_isUnif_of_field
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_unif_mem_nonZeroDivisors
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_unif_mem

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
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (K : Type*) {L : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [Algebra K L] [IsScalarTower O K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (ζ : Pts O L) : IsDVRAt ζ := by
  have : IsDedekindDomain ↥(As O L) := integralClosure.isDedekindDomain O K L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h : IsUnif L ϖ := isUnif_of_field K hϖ
  have hne : ζ.asIdeal ≠ ⊥ := by
    intro h0
    have h1 := unif_mem h ζ
    rw [h0, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero (unif_mem_nonZeroDivisors h) h1
  have hd : IsDomain (Loc ζ) := inferInstance
  exact ⟨hd, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hne _⟩
end Formalism.MainNotions.Gaps.EtaleWeightGaps
