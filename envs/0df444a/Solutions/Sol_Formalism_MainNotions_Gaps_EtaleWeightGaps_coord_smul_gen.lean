-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coord_smul_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:52:37.982091+00:00
-- url     : https://prove2.me/submissions/ff496073-e04c-42af-ace6-68ace65939ef

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
variable {V : Type*} [AddCommGroup V] [Module A V]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution {e : V} (he : IsGen A e) (a : A) : coord e (a • e) = a :=
  Function.leftInverse_invFun (f := fun a : A => a • e) he.1 a
end Formalism.MainNotions.Gaps.EtaleWeightGaps
