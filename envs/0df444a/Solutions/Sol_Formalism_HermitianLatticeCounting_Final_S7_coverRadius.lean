-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S7.coverRadius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:32.638969+00:00
-- url     : https://prove2.me/submissions/a832353f-5f8a-482a-bb36-ffa6974db032

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDeltaL1Bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_covering_radius_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.CoverRadius := Formalism.HermitianLatticeCounting.P.covering_radius_bound
end Formalism.HermitianLatticeCounting.Final.S7
