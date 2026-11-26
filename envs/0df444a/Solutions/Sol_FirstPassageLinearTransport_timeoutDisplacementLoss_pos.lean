-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutDisplacementLoss_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:19.019426+00:00
-- url     : https://prove2.me/submissions/959d4d5b-3562-4c2d-97f9-a410b6d0d66b

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_endpoint_probability_eq_logThreeTwo
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    0 < timeoutDisplacementLoss K₀ := by
  have hp : 0 < logThreeTwo := by
    rw [← endpoint_probability_eq_logThreeTwo]
    linarith [firstPassageEndpointDisplacement_pos]
  unfold timeoutDisplacementLoss
  positivity
end FirstPassageLinearTransport
