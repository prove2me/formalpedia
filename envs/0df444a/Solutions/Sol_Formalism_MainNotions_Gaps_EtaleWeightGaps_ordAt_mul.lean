-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:06.115839+00:00
-- url     : https://prove2.me/submissions/ff5f3d41-32f7-4100-acd1-5160f3f068a3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_mul

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
theorem _root_.solution (n m : ℕ) (a b : ↥(As O A)) :
    ordAt ϖ ζ (n + m) (a * b) = ordAt ϖ ζ n a + ordAt ϖ ζ m b := by
  unfold ordAt
  rw [vL_mul]
  have h1 : (vL ζ a + vL ζ b).map (Nat.cast : ℕ → ℤ)
      = (vL ζ a).map (Nat.cast : ℕ → ℤ) + (vL ζ b).map (Nat.cast : ℕ → ℤ) :=
    ENat.map_add (Nat.castAddMonoidHom ℤ) _ _
  have h2 : ((-(((n + m : ℕ) : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ)
      = ((-((n : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ) + ((-((m : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [← WithTop.coe_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, add_add_add_comm]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
