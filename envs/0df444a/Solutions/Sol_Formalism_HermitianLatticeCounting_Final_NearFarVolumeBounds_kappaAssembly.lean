-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.kappaAssembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:59.011135+00:00
-- url     : https://prove2.me/submissions/cc1372fa-63e6-4241-ae7f-69f7dee79e78

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_KappaConstantAssembly
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_kappa_constant_assembly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
namespace Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.KappaAssembly := Formalism.HermitianLatticeCounting.P.kappa_constant_assembly
end Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
