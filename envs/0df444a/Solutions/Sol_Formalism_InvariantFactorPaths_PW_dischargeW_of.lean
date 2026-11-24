-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.dischargeW_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:49:51.271219+00:00
-- url     : https://prove2.me/submissions/57221afd-f35f-4b7b-983a-ef89bf213f3b

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_pow_smul_mem_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M Formalism.GM
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (h : WeylP) : DischargeW := by
  intro p _ N r LL e1 he
  have h0 := h p N r LL
  unfold Formalism.GM.M.HypW at h0 ⊢
  intro j hj la x hx hxI
  exact pow_smul_mem_of_le _ he (h0 j hj la x hx hxI)
end Formalism.InvariantFactorPaths.PW
