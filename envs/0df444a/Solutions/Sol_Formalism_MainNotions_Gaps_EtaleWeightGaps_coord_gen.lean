-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coord_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:16.862879+00:00
-- url     : https://prove2.me/submissions/5b381439-476f-426d-9491-ea6da3b5a7d1

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
theorem _root_.solution {e : V} (he : IsGen A e) : (coord e e : A) = 1 := by
  simpa using coord_smul_gen he (1 : A)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
