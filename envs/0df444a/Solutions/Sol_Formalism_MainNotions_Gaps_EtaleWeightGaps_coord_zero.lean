-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:20.311131+00:00
-- url     : https://prove2.me/submissions/cabb83ed-f56a-443a-bcba-f0818a4bf6e1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_smul_gen

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
theorem _root_.solution {e : V} (he : IsGen A e) : (coord e (0 : V) : A) = 0 := by
  simpa using coord_smul_gen he (0 : A)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
