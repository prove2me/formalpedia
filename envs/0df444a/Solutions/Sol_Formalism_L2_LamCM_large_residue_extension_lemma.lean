-- Prove2me | solution 1 for Formalism.L2.LamCM.large_residue_extension_lemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:59:16.19686+00:00
-- url     : https://prove2.me/submissions/943c5eca-d2a2-435d-a1e0-a73001c466c4

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Theorems.Thm_Formalism_L2_LamCM_LemmaG_of
import Theorems.Thm_Formalism_L2_LamCM_largeResidueExtension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution : LemmaG := LemmaG_of largeResidueExtension
end Formalism.L2.LamCM
