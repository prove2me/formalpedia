-- Prove2me | solution 1 for Formalism.FG.coeff_bound_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:12.06431+00:00
-- url     : https://prove2.me/submissions/63cf9f51-606d-433d-8131-20a978c71200

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.CoeffBoundV.{u, v, w} := Formalism.FG.CoefficientBoundsFormalGroupWitt.main.{u, v, w}
end Formalism.FG
