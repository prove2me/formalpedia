-- Prove2me | solution 1 for Formalism.LIFT.wDNonempty_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:01.171674+00:00
-- url     : https://prove2.me/submissions/02804373-b355-4f83-86b9-0be9e1e2b9cf

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
open Polynomial
namespace Formalism.LIFT
theorem _root_.solution : WDNonempty := by
  intro ℓ _ u
  refine ⟨polyBase ℓ u, polyWD ℓ u, rfl, ?_, ?_⟩
  · exact top_ne_bot
  · exact not_isUnit_X
end Formalism.LIFT
