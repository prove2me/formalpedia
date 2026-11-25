-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.transfer_product_monic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:43.028846+00:00
-- url     : https://prove2.me/submissions/18001850-e4bb-4768-b1a1-bbc8afbd9449

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferProductMonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Misc_tProdMonic_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.I.TProdMonic := Formalism.FourierDecayAlt.P.Misc.tProdMonic_holds
end Formalism.FourierDecayAlt.P
