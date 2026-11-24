-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.relIndexInter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:10.100398+00:00
-- url     : https://prove2.me/submissions/456ded97-c727-453b-b4fd-735bf8711d11

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_LiftFixesBaseVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_relIndex_intersection


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.RelIndexInter := Formalism.HermitianLatticeCounting.P.relIndex_intersection
end Formalism.HermitianLatticeCounting.Final.S6
