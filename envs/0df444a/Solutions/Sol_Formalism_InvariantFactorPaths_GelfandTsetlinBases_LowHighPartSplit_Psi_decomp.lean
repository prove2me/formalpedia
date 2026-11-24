-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit.Psi_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:46.366398+00:00
-- url     : https://prove2.me/submissions/8c53b004-c78e-4c3c-a5cd-9bf1fa36e633

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_decomp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_Psi_high
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_LowHighPartSplit_high_zero

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
theorem _root_.solution {i : ℕ} (hS : ∀ j, j ∈ S ↔ j < i) (G : MvPolynomial (ℕ × Fin n) k) :
    Psi isVec S G = ∑ β ∈ G.support.image (highP i),
      Psi isVec S (Gc i G β) * monomial (β.mapDomain Sum.inl) 1 := by
  conv_lhs => rw [decomp i G]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [map_mul, Psi_high isVec S (high_zero S hS hβ)]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.LowHighPartSplit
