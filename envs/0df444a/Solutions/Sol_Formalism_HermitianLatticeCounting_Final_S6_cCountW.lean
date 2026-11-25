-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.cCountW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:59.190409+00:00
-- url     : https://prove2.me/submissions/fee2db33-c0eb-405b-a888-6b81775cf568

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeWAsm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_colon_count_weighted


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.CCountW := Formalism.HermitianLatticeCounting.P.colon_count_weighted
end Formalism.HermitianLatticeCounting.Final.S6
