-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.Psi_Gc_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:23.483188+00:00
-- url     : https://prove2.me/submissions/11b236d7-fd76-4a04-b1dd-5a87b359ca11

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_lowerUnipotent_symm_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_low

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
theorem _root_.solution {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (G : MvPolynomial (ℕ × Fin n) k) (β : ℕ × Fin n →₀ ℕ) :
    Psi isVec S (Gc i G β) ∈ supported (GenField k n) (loSet n S) := by
  simp only [Gc, map_sum]
  exact Subalgebra.sum_mem _ fun e _ =>
    Psi_low isVec S (fun j a hj => by rw [lowerUnipotent_symm_apply, if_neg ((hS j).not.mp hj)]) _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
