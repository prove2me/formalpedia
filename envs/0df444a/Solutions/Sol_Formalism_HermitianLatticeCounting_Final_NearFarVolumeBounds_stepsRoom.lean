-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.stepsRoom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:41.094977+00:00
-- url     : https://prove2.me/submissions/f8779028-4992-42aa-896c-92a2327a5d55

import Definitions.Def_Formalism_FlagUnipotentLattices_CoveringRadius2
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_KappaConstantAssembly
import Definitions.Def_Formalism_FlagUnipotentLattices_KappaAssemblyOf
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_room_for_iterations


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.StepsRoom := Formalism.HermitianLatticeCounting.P.room_for_iterations
end Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
