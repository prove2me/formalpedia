-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.product_domination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:47:34.667177+00:00
-- url     : https://prove2.me/submissions/4f2bc2d6-41a3-42fa-be34-039a50b3d516

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_ProductDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.ProductDomination := Jx7.t_ProductDomination
end Formalism.FourierDecayAlt.P
