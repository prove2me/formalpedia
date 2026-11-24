-- Prove2me | solution 1 for Formalism.G0.type_two_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:39.028805+00:00
-- url     : https://prove2.me/submissions/386e38b9-c1b2-4182-8021-45102175e705

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
import Theorems.Thm_Formalism_G0_typeIIUp_of
import Theorems.Thm_Formalism_G0_countSubspacesEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : TypeIIUp := typeIIUp_of countSubspacesEq
end Formalism.G0
