-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.subGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:01:15.046201+00:00
-- url     : https://prove2.me/submissions/9c91d188-96d8-499f-910f-24c3f06be3b4

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeWAsm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_submodule_generator_count


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.SubGen := Formalism.HermitianLatticeCounting.P.submodule_generator_count
end Formalism.HermitianLatticeCounting.Final.S6
