-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.quotCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:01:08.52443+00:00
-- url     : https://prove2.me/submissions/f4b76320-cf25-4ef1-81a6-e10f64b9845a

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeWAsm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_height_loss_bound


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.QuotCard := Formalism.HermitianLatticeCounting.P.height_loss_bound
end Formalism.HermitianLatticeCounting.Final.S6
