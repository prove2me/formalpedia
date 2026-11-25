-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt.redAs_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:20:43.839362+00:00
-- url     : https://prove2.me/submissions/88af7409-4d37-43fd-a2a9-84aa4b29a02d

import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_IsIntegralOfAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
variable (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
theorem _root_.solution (m : Ideal A) (a : ↥(As O A)) : (redAs O A m a : A ⧸ m) = Ideal.Quotient.mk m a := rfl
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Hunt
