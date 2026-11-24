-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.Psi_X_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.941802+00:00
-- url     : https://prove2.me/submissions/69ea22c2-75a8-4747-b13c-dd43a944d905

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_apply

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
theorem _root_.solution {j : ℕ} (hj : j ∈ S) (a : Fin n) :
    Psi isVec S (X (j, a) : MvPolynomial (ℕ × Fin n) k) ∈ supported (GenField k n) (loSet n S) := by
  have hgen : ∀ Mt : Matrix (Fin n) (Fin n) (GenField k n),
      Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
        (Mt.map C) a ∈ supported (GenField k n) (loSet n S) := by
    intro Mt
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (X_mem_supported.mpr ⟨j, b, hj, rfl⟩)
      (by rw [← algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _)
  simp only [Psi_apply, genH, rename_X, map_X, sharpHom, aeval_X, if_pos hj]
  split_ifs
  · exact hgen _
  · rw [← Matrix.transpose_map]
    exact hgen _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
