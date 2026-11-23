-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ep_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:14.820357+00:00
-- url     : https://prove2.me/submissions/fda65608-78e2-4e7c-ad43-e5e9fa62d551

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_zero_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_unif_mem
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coe_ep

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
theorem _root_.solution (h : IsUnif A ϖ) : 0 < ep ϖ ζ := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have h1 := coe_ep ζ h
  rw [h0, Nat.cast_zero, eq_comm, vL_eq_zero_iff] at h1
  exact h1 (unif_mem h ζ)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
