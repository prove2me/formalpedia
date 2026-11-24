-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.wach_lattice_nonempty_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:54.006161+00:00
-- url     : https://prove2.me/submissions/2d0f9c45-becf-4008-816f-098ef5b0dd17

import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeLIFT
import Theorems.Thm_Formalism_LIFT_wDNonempty_proof


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : NonemptyU := by
  intro p _ u
  obtain ⟨B, W, hu, hN, hX⟩ := LIFT.wDNonempty_proof p u
  subst hu
  refine ⟨baseOfLIFT B, ofLIFT W (lift_gamma_invariant_lattice p _ B 0 _ W), rfl, hN, hX, B.γX, ?_⟩
  obtain ⟨t, ht, h⟩ := B.γQ
  refine ⟨1 + B.X * t, ht, ⟨t, rfl⟩, ?_⟩
  show B.γA B.Q = (1 + B.X * t) * B.Q
  rw [h, mul_comm]
end Formalism.CoboundaryTransfers
