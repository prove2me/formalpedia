-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.liftIsoW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:12.815795+00:00
-- url     : https://prove2.me/submissions/fa41e546-eea3-46a5-b1db-1203446bd799

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_LiftFixesBaseVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lifting_isometry_weight


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftIsoW := Formalism.HermitianLatticeCounting.P.lifting_isometry_weight
end Formalism.HermitianLatticeCounting.Final.S6
