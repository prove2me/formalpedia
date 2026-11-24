-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:29.202562+00:00
-- url     : https://prove2.me/submissions/601edc4a-cfd0-4b50-ab4a-1f30088da9c7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coe_ep
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
variable (ζ : Pts O A) [IsDVRAt ζ]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (h : IsUnif A ϖ) : ord ϖ ζ (algebraMap O A ϖ) = ((ep ϖ ζ : ℤ) : WithTop ℤ) := by
  have hm : algebraMap O A ϖ ∈ As O A := (algebraMap O ↥(As O A) ϖ).2
  rw [ord_of_mem ζ h hm]
  have : (⟨algebraMap O A ϖ, hm⟩ : ↥(As O A)) = algebraMap O ↥(As O A) ϖ :=
    rfl
  rw [this, ← coe_ep ζ h, ENat.map_natCast]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
