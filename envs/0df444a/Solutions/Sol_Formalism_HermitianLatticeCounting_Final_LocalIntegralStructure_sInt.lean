-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.sInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:03:59.64519+00:00
-- url     : https://prove2.me/submissions/62ba3ee6-a130-4a19-85c7-54c3c28f206b

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_FlagUnipotentLattices_UnitSumBound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ConstantProductFormula
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s_integrality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := Formalism.HermitianLatticeCounting.P.s_integrality
end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
