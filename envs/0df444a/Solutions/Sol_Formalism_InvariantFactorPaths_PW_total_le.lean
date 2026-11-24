-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.total_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:02.058671+00:00
-- url     : https://prove2.me/submissions/a0807395-7cbc-400c-81c3-e3c924f221f7

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_Discharge

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
theorem _root_.solution {N : ℕ} (LL : Letters N) (b : ℕ) (h : ∀ x, LL.deg x ≤ b) : LL.total ≤ b * N := by
  unfold Letters.total
  calc ∑ i, LL.deg i ≤ ∑ _i : Fin N, b := Finset.sum_le_sum (fun i _ => h i)
    _ = b * N := by simp [mul_comm]
end Formalism.InvariantFactorPaths.PW
