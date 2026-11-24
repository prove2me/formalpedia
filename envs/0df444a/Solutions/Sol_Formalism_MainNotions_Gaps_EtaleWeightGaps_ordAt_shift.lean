-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:08.145418+00:00
-- url     : https://prove2.me/submissions/67842201-41d0-4bcf-b3eb-36b1ace450d9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_pow
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
theorem _root_.solution (h : IsUnif A ϖ) (n k : ℕ) (a : ↥(As O A)) :
    ordAt ϖ ζ (n + k) ((algebraMap O ↥(As O A) ϖ) ^ k * a) = ordAt ϖ ζ n a := by
  unfold ordAt
  rw [vL_mul, vL_pow, ← coe_ep ζ h]
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    have h1 : k • (ep ϖ ζ : ℕ∞) + (j : ℕ∞) = ((k * ep ϖ ζ + j : ℕ) : ℕ∞) := by
      push_cast; simp [nsmul_eq_mul]
    rw [h1, ENat.map_natCast, ENat.map_natCast, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    push_cast
    ring
end Formalism.MainNotions.Gaps.EtaleWeightGaps
