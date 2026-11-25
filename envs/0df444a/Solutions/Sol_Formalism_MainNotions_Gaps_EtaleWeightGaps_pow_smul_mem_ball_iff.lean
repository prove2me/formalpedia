-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.pow_smul_mem_ball_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:19.793804+00:00
-- url     : https://prove2.me/submissions/1b62b1d9-45b9-4d2a-a6d5-ecf19eaa58e5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_unif
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_smul
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
    (k : ℕ) (v : V) :
    (algebraMap O A ϖ) ^ k • v ∈ ball ϖ e c ↔
      v ∈ ball ϖ e (fun ζ => c ζ + (k : ℤ) * (ep ϖ ζ : ℤ)) := by
  rw [mem_ball_iff _ h he, mem_ball_iff _ h he]
  refine forall_congr' (fun ζ => ?_)
  rw [ordV_smul c ζ h he, ord_pow ζ h, ord_unif ζ h, ordV, ordV, ← WithTop.coe_nsmul,
    nsmul_eq_mul, WithTop.coe_add, add_left_comm, add_comm (((c ζ : ℤ) : WithTop ℤ))]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
