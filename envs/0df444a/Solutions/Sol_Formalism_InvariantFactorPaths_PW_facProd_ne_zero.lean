-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.facProd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:23.297849+00:00
-- url     : https://prove2.me/submissions/0fbe3efa-48ce-4b1f-b22f-af0b546ff2c4

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : ℚ_[p])) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast Nat.factorial_ne_zero _
end Formalism.InvariantFactorPaths.PW
