-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S7.posTypeBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:15:53.437839+00:00
-- url     : https://prove2.me/submissions/c89bb2d8-bf9b-4052-8414-168bb8e989b2

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDeltaL1Bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_positive_type_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.PosTypeBound := Formalism.HermitianLatticeCounting.P.positive_type_bound
end Formalism.HermitianLatticeCounting.Final.S7
