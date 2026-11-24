-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.isGen_units_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:22.912957+00:00
-- url     : https://prove2.me/submissions/e197d7ce-c962-438d-ae8f-2fd0014f1e3c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall

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
theorem _root_.solution (he : IsGen A e) (u : Aˣ) : IsGen A ((u : A) • e) := by
  have : (fun a : A => a • ((u : A) • e)) = (fun a : A => a • e) ∘ (fun a : A => a * u) := by
    funext a
    simp [smul_smul]
  rw [IsGen, this]
  exact he.comp (Units.mulRight_bijective u)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
