-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_ballO_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:43.961744+00:00
-- url     : https://prove2.me/submissions/b6def79f-d6be-4a7d-aca1-34aeb85471f9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
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
theorem _root_.solution [Module O V] [IsScalarTower O A V] [∀ ζ : Pts O A, IsDVRAt ζ]
    (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ballO ϖ e c ↔ ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v :=
  mem_ball_iff c h he v
end Formalism.MainNotions.Gaps.EtaleWeightGaps
