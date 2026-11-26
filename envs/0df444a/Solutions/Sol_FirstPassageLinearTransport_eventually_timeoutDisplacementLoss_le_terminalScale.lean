-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutDisplacementLoss_le_terminalScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:27.184331+00:00
-- url     : https://prove2.me/submissions/5068ca19-ea88-407d-962f-5f691567d43a

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointProfile
import Definitions.Def_FirstPassageLinearTransport_RankTransportAsymptotics
import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEndpointDisplacement_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (K₀ : ℝ) :
    ∀ᶠ L : ℕ in atTop,
      2 * timeoutDisplacementLoss K₀ ≤
        firstPassageEndpointDisplacement * (L : ℝ) := by
  have hT : Tendsto
      (fun L : ℕ => firstPassageEndpointDisplacement * (L : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop
      firstPassageEndpointDisplacement_pos
  exact (tendsto_atTop.1 hT) (2 * timeoutDisplacementLoss K₀)
end FirstPassageLinearTransport
