-- Prove2me | solution 1 for Formalism.L2.LamCM.subst_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:15:14.557887+00:00
-- url     : https://prove2.me/submissions/07c83478-b7f8-4940-a167-01d10cc261d6

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Theorems.Thm_Formalism_L2_LamCM_substFr_one
import Theorems.Thm_Formalism_L2_LamCM_substFr_substFr
import Theorems.Thm_Formalism_L2_LamCM_evalFr_substFr

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
theorem _root_.solution : SubstEval := by
  intro R _ B _ m P U
  refine ⟨fun Y => evalFr_substFr U P Y, fun hU => ?_, substFr_one P⟩
  rw [substFr_substFr]
  have h : (fun b => U b * (U b)⁻¹) = fun b => (1 : Matrix (Fin (m b)) (Fin (m b)) R) :=
    funext fun b => Matrix.mul_nonsing_inv _ (hU b)
  rw [h, substFr_one]
end Formalism.L2.LamCM
