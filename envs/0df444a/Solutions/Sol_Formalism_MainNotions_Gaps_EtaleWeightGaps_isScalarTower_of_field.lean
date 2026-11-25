-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.isScalarTower_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:47.903365+00:00
-- url     : https://prove2.me/submissions/15a42a08-9660-491e-b5d5-ddc91df45158

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
theorem _root_.solution (K : Type*) [Field K] [Algebra O K] [Algebra K A]
    [IsScalarTower O K A] [Module K V] [IsScalarTower K A V] [Module O V] [IsScalarTower O K V] :
    IsScalarTower O A V :=
  ⟨fun o a v => by
    rw [← algebraMap_smul K o a, ← algebraMap_smul K o (a • v), smul_assoc]⟩
end Formalism.MainNotions.Gaps.EtaleWeightGaps
