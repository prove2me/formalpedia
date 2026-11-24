-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.norm_pow_p_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:18.083799+00:00
-- url     : https://prove2.me/submissions/0178d285-3aec-4087-ae2e-9cd6ece59dbd

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (k : ℕ) : ‖(p : ℚ_[p]) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le
end Formalism.InvariantFactorPaths.PW
