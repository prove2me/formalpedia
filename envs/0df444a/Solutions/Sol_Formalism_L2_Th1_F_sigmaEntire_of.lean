-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaEntire_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:03.665174+00:00
-- url     : https://prove2.me/submissions/a951397c-8734-4edd-9b0a-a6a71b092c91

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_differentiable_tprod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open SigmaBasic
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SigmaProdLU) : SigmaEntire := by
  intro L
  unfold wSigma
  exact differentiable_id.mul (differentiable_tprod h L)
end Formalism.L2.Th1.F
