-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.monomial_mem_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:16.311513+00:00
-- url     : https://prove2.me/submissions/61d264f2-1272-494e-ba3c-4b31934eae4d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (m : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    monomial m a ∈ Pol p r (⟨LL.vec, fun i => ∑ c, m (i, c)⟩ : Letters N) := by
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro d hd
  have := MvPolynomial.support_monomial_subset hd
  rw [Finset.mem_singleton] at this
  subst this
  intro i
  rfl
end Formalism.InvariantFactorPaths.PW
