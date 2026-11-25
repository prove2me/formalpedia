-- Prove2me | solution 1 for Formalism.G0.TypeIIDownP.gb_one_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:44.654111+00:00
-- url     : https://prove2.me/submissions/93abe4c0-97ba-4531-92ca-5d4b4cf70c6c

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
import Theorems.Thm_Formalism_G0_TypeIIDownP_gb_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TypeIIDownP
open QVandermondeP
namespace Formalism.G0.TypeIIDownP
theorem _root_.solution (q : ℕ) : gaussBinom q 1 1 = 1 := gb_self q 1
end Formalism.G0.TypeIIDownP
