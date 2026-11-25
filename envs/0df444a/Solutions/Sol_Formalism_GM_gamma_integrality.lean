-- Prove2me | solution 1 for Formalism.GM.gamma_integrality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:54:24.869677+00:00
-- url     : https://prove2.me/submissions/c4005241-d808-477b-a045-92516af9833d

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_gamma_integrality_of_contraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution : M.GamInt := gammaIntegralityLemmas.gamma_integrality_of_contraction
end Formalism.GM
