-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.polarInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:27:45.272319+00:00
-- url     : https://prove2.me/submissions/1b3cef4f-7c66-433e-adb9-4ae133023cfc

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_KappaConstantAssembly
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_polar_decomposition_inverse


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.PolarInv := Formalism.HermitianLatticeCounting.P.polar_decomposition_inverse
end Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
