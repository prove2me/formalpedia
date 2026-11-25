-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV_units_smul_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:15:05.196442+00:00
-- url     : https://prove2.me/submissions/0b8f8e71-23b4-4fe7-af9e-845d05ce189b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_units_smul

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
variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (u : Aˣ)
    (v : V) : ordV ϖ ζ e c v = ord ϖ ζ (u : A) + ordV ϖ ζ ((u : A) • e) c v := by
  rw [ordV, ← coord_units_smul he u, ord_mul ζ h, ordV, add_comm (ord ϖ ζ (coord _ v)), add_assoc]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
