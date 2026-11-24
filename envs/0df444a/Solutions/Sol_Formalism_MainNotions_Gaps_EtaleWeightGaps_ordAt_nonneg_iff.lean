-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:07.2646+00:00
-- url     : https://prove2.me/submissions/c21c66c2-2d21-42e2-a7de-32b76958a1aa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
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
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (n : ℕ) (a : ↥(As O A)) :
    0 ≤ ordAt ϖ ζ n a ↔ vL ζ ((algebraMap O ↥(As O A) ϖ) ^ n) ≤ vL ζ a := by
  unfold ordAt
  rw [vL_pow, ← coe_ep ζ h]
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    have h1 : n • (ep ϖ ζ : ℕ∞) = ((n * ep ϖ ζ : ℕ) : ℕ∞) := by
      push_cast; simp [nsmul_eq_mul]
    rw [h1, ENat.map_natCast, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe,
      Nat.cast_le]
    constructor
    · intro hh
      have : ((n * ep ϖ ζ : ℕ) : ℤ) ≤ (j : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · intro hh
      have : ((n * ep ϖ ζ : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast hh
      push_cast at this
      linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps
