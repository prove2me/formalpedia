-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.kappa_constant_assembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:57.043927+00:00
-- url     : https://prove2.me/submissions/38c4ff25-4974-48ce-a319-a65ceed3f7ea

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_LatticeRigidity_RecursionUnrestrictedFalse
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_KappaConstantAssembly
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_kappaAssembly_of
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_volume_ratio


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.KappaAssembly := kappaAssembly_of volume_ratio
end Formalism.HermitianLatticeCounting.P
