-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.iotaDetermined
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:00:48.356384+00:00
-- url     : https://prove2.me/submissions/49a2cae8-b857-4fb7-a5ba-d1d118c1f871

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeWAsm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_embedding_determined_by_restriction


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.IotaDetermined := Formalism.HermitianLatticeCounting.P.embedding_determined_by_restriction
end Formalism.HermitianLatticeCounting.Final.S6
