-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normalFormStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:38.743669+00:00
-- url     : https://prove2.me/submissions/45a920c2-6acd-46ae-a36f-668ea9b15681

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_wedgeMapInLieAlgebra
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_memOfOrthogonalOrthogonal
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_nFStep_of

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFStep := nFStep_of wedgeMapInLieAlgebra memOfOrthogonalOrthogonal
end Formalism.HermitianLatticeCounting.P
