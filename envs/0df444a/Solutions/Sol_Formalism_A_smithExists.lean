-- Prove2me | solution 1 for Formalism.A.smithExists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:20.156919+00:00
-- url     : https://prove2.me/submissions/e42e320d-ee27-4e48-ba8c-3fec40103a83

import Definitions.Def_Formalism_SmithDeterminants_DefsGram
import Definitions.Def_Formalism_SmithDeterminants_DivisibilityChains_SmithExists
import Definitions.Def_Formalism_SmithDeterminants_TruncationChainBoundNonnegExponents
import Theorems.Thm_Formalism_A_smith_form_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.A
namespace Formalism.A
theorem _root_.solution : SmithExists := smith_form_exists
end Formalism.A
