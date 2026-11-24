-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.gl_action_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:39.131367+00:00
-- url     : https://prove2.me/submissions/726d79f4-00d1-4fe9-9967-ceda97c08edc

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_WmMulWmComm
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_GX_E
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_coeff_GX_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : GXExists := by
  intro p _ K s LL c hv
  exact ⟨GX p LL c hv, GX_E LL c hv, fun μ x m => coeff_GX_comp LL c hv μ x m⟩
end Formalism.InvariantFactorPaths.L4
