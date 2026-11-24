-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.wExp_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:46.932886+00:00
-- url     : https://prove2.me/submissions/0bb56c52-3779-4268-82d4-01fa9b1b890c

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
theorem _root_.solution (last : Bool) (e f : LVar ℕ Empty n →₀ ℕ) :
    wExp isVec S last (e + f) = wExp isVec S last e + wExp isVec S last f := by
  simp only [wExp]
  change (e + f).sum (fun x d => (d : ℤ) * wtX isVec S last x) =
    e.sum (fun x d => (d : ℤ) * wtX isVec S last x) + f.sum (fun x d => (d : ℤ) * wtX isVec S last x)
  rw [Finsupp.sum_add_index']
  · intro x
    simp
  · intro x a b
    push_cast
    ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
