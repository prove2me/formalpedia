-- Prove2me | solution 1 for Formalism.G0.countAboveRangeCodimFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:28.326841+00:00
-- url     : https://prove2.me/submissions/12c5bdbe-3c46-45e9-bd6c-13ae6e26be8e

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIDown
import Theorems.Thm_Formalism_G0_typeIIDown_of
import Theorems.Thm_Formalism_G0_countSubspacesEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : TypeIIDown :=
  typeIIDown_of countSubspacesEq
end Formalism.G0
