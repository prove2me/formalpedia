-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordAt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:04.670259+00:00
-- url     : https://prove2.me/submissions/c63474df-d980-4b56-8bd8-16afd574ff19

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_add

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
theorem _root_.solution (n : ℕ) (a b : ↥(As O A)) :
    min (ordAt ϖ ζ n a) (ordAt ϖ ζ n b) ≤ ordAt ϖ ζ n (a + b) := by
  unfold ordAt
  rw [min_add_add_right]
  refine add_le_add_left ?_ _
  have hm : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) := ENat.monotone_map_iff.2 Nat.mono_cast
  rw [← hm.map_min]
  exact hm (vL_add ζ a b)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
