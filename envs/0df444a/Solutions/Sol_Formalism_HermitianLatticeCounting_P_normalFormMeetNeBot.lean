-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normalFormMeetNeBot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:28.91481+00:00
-- url     : https://prove2.me/submissions/59690253-9c8b-4a81-83e9-d8530ad31930

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lastVectorNotMemSup
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normalFormStep
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_nFCaseA_of_lastVectorNotMemSup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFCaseA := nFCaseA_of_lastVectorNotMemSup normalFormStep lastVectorNotMemSup
end Formalism.HermitianLatticeCounting.P
