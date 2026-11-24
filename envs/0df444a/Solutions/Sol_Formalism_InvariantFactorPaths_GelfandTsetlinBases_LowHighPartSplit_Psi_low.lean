-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.Psi_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:50.422657+00:00
-- url     : https://prove2.me/submissions/53b871bc-5f6a-403d-94cd-3e3f9964ad78

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_X_low
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
variable {n : ℕ}
variable {k : Type*} [Field k] (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
theorem _root_.solution {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∉ S → e (j, a) = 0) (c : k) :
    Psi isVec S (monomial e c) ∈ supported (GenField k n) (loSet n S) := by
  rw [Psi_monomial]
  refine Subalgebra.mul_mem _ (by rw [← algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun x hx => Subalgebra.pow_mem _ ?_ _)
  obtain ⟨j, a⟩ := x
  have hj : j ∈ S := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hx) (he j a h)
  exact Psi_X_low isVec S hj a
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
