-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.liftUnitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:13.188853+00:00
-- url     : https://prove2.me/submissions/e2430456-3bee-436a-906c-9b3ac9e463f0

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_LiftFixesBaseVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lifting_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S6
namespace Formalism.HermitianLatticeCounting.Final.S6
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftUnitary := Formalism.HermitianLatticeCounting.P.lifting_unitary
end Formalism.HermitianLatticeCounting.Final.S6
