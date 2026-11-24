-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.highest_weight_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:53.710812+00:00
-- url     : https://prove2.me/submissions/f937f146-3c44-4906-9c3c-8679fb2cecca

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
import Theorems.Thm_Formalism_L2_G_Model_TS_fockR_hw_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution : HWNorm := fockR_hw_norm
end Formalism.L2.G.Model.TS
