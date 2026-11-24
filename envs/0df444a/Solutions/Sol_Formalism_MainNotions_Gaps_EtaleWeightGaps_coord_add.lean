-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coord_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:14.466115+00:00
-- url     : https://prove2.me/submissions/9e10e29e-9572-482f-a546-78fe4ee5cebd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_smul_self
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
theorem _root_.solution {e : V} (he : IsGen A e) (v w : V) :
    (coord e (v + w) : A) = coord e v + coord e w := by
  conv_lhs => rw [← coord_smul_self he v, ← coord_smul_self he w, ← add_smul]
  exact coord_smul_gen he _
end Formalism.MainNotions.Gaps.EtaleWeightGaps
