-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.wExp_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:58.916102+00:00
-- url     : https://prove2.me/submissions/3d51db92-75c7-4cb8-9bf1-624657d631f2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit

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
theorem _root_.solution (last : Bool) {e : ℕ × Fin n →₀ ℕ} (he : ∀ j a, j ∈ S → e (j, a) = 0) :
    wExp isVec S last (e.mapDomain Sum.inl : LVar ℕ Empty n →₀ ℕ) = 0 := by
  simp only [wExp]
  change (e.mapDomain Sum.inl).sum (fun x d => (d : ℤ) * wtX isVec S last x) = 0
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring)]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨j, a⟩ := x
  have hj : j ∉ S := fun h => (Finsupp.mem_support_iff.mp hx) (he j a h)
  simp [wtX, hj]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
