-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.idealCountLeWAsm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:00:44.447337+00:00
-- url     : https://prove2.me/submissions/9ecbca77-b61c-47de-94dd-af75b85cfc5f

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeWAsm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ideal_count_le_weighted_of_hyp


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.IdealCountLeW' := Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted_of_hyp
end Formalism.HermitianLatticeCounting.Final.S6
