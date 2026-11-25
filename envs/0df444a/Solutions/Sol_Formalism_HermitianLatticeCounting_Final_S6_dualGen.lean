-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.dualGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:26.809921+00:00
-- url     : https://prove2.me/submissions/332d5fe8-23e5-4097-b12e-6670dc69e20c

import Definitions.Def_Formalism_FlagUnipotentLattices_OmSumLong
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeDataCounting
import Definitions.Def_Formalism_FlagUnipotentLattices_IotaCountFullAsm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_generators


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.DualGen := Formalism.HermitianLatticeCounting.P.dual_generators
end Formalism.HermitianLatticeCounting.Final.S6
