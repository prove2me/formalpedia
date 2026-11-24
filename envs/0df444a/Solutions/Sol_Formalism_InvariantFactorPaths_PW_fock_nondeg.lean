-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.fock_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:58:47.995811+00:00
-- url     : https://prove2.me/submissions/743e5bac-23f0-480b-81a3-d844c9f7ac89

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_facProd_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_monomial_right

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
theorem _root_.solution (F : MvPolynomial σ ℚ_[p]) (h : ∀ G, fock p F G = 0) : F = 0 := by
  ext m
  have h1 := h (monomial m 1)
  rw [fock_monomial_right, mul_one] at h1
  rw [coeff_zero]
  exact (mul_eq_zero.1 h1).resolve_right (facProd_ne_zero m)
end Formalism.InvariantFactorPaths.PW
