-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure.classNumberBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:29.042002+00:00
-- url     : https://prove2.me/submissions/23bb2e25-e361-47ab-8cb2-d04314441aed

import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Definitions.Def_Formalism_FlagUnipotentLattices_ArithmeticIdentityEntries
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_class_number_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_bound
end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
