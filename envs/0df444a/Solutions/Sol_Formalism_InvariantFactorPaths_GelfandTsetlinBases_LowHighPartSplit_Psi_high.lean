-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.Psi_high
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:53.587141+00:00
-- url     : https://prove2.me/submissions/d20284eb-e53a-4666-9283-a2ad3c4593b2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_X_high
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
theorem _root_.solution {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∈ S → e (j, a) = 0) :
    Psi isVec S (monomial e (1 : k)) = monomial (e.mapDomain Sum.inl) 1 := by
  rw [Psi_monomial, map_one, map_one, one_mul, ← rename_monomial, monomial_eq, C_1, one_mul,
    Finsupp.prod, map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  rw [map_pow, rename_X]
  obtain ⟨j, a⟩ := x
  have hj : j ∉ S := fun h => (Finsupp.mem_support_iff.mp hx) (he j a h)
  rw [Psi_X_high isVec S hj a]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
