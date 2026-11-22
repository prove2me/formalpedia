-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.pow_smul_mem_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:49.412345+00:00
-- url     : https://prove2.me/submissions/2b66105b-90ef-47fc-b546-4cef20efc161

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] {σ : Type} (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    {k e : ℕ} (hke : k ≤ e) {y : MvPolynomial σ ℚ_[p]} (hy : ((p : ℚ_[p]) ^ k) • y ∈ L) :
    ((p : ℚ_[p]) ^ e) • y ∈ L := by
  have h := L.smul_mem ((p : ℤ_[p]) ^ (e - k)) hy
  rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ (e - k)), smul_smul] at h
  have e2 : ((p : ℚ_[p]) ^ e) = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) ^ (e - k)) * (p : ℚ_[p]) ^ k := by
    rw [map_pow, map_natCast, ← pow_add, Nat.sub_add_cancel hke]
  rw [e2]
  exact h
end Formalism.InvariantFactorPaths.PW
