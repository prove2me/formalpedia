-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.dischargeE_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:16.73984+00:00
-- url     : https://prove2.me/submissions/a6f96621-6fb6-40d5-969a-30da08d2f733

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_kapC_mono
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
theorem _root_.solution (h : ExtP) : DischargeE := by
  intro p _ N r LL ρ e1 he
  have h0 := h p N r LL ρ
  unfold Formalism.GM.M.HypE at h0 ⊢
  intro j hj la
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := h0 j hj la
  have hk : kapC p (r - 1) LL.total ≤ e1 := (kapC_mono (Nat.sub_le r 1) le_rfl).trans he
  exact ⟨P, h1, h2, h3, h4, fun F hF hW => pow_smul_mem_of_le _ hk (h5 F hF hW)⟩
end Formalism.InvariantFactorPaths.PW
