-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S7.finalSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:58.610012+00:00
-- url     : https://prove2.me/submissions/b9c6b891-3e12-4500-a9ea-0407945debe7

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDeltaL1Bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_final_sum_near_far


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S7
namespace Formalism.HermitianLatticeCounting.Final.S7
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.FinalSum := Formalism.HermitianLatticeCounting.P.final_sum_near_far
end Formalism.HermitianLatticeCounting.Final.S7
