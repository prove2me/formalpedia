-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S7.conjInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:40:44.156712+00:00
-- url     : https://prove2.me/submissions/00d7c1f0-e8fa-4f0a-a0c1-e4b51eeb68be

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDeltaL1Bound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_conjugation_invariant_measure


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.ConjInv := Formalism.HermitianLatticeCounting.P.conjugation_invariant_measure
end Formalism.HermitianLatticeCounting.Final.S7
