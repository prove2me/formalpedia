-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.fock_monomial_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:18.890053+00:00
-- url     : https://prove2.me/submissions/30aa5d92-89d0-4f82-b49e-fa34b00422a2

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_eq_sum__18511f081048
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_symm__e96ddd2ea090

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
theorem _root_.solution (F : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) (a : ℚ_[p]) :
    fock p F (monomial m a) = F.coeff m * a * (m.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  rw [fock_symm', fock_eq_sum' _ _ {m} support_monomial_subset, Finset.sum_singleton,
    coeff_monomial, if_pos rfl]
  ring
end Formalism.InvariantFactorPaths.PW
