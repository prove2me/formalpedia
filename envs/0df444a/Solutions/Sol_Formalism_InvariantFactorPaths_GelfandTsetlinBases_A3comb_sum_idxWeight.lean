-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.sum_idxWeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.854052+00:00
-- url     : https://prove2.me/submissions/198eec5c-b70e-402d-aed1-525c1ea80118

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_idxWeight_eq

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ) (hS : ∀ c, c ∉ S → I c = ∅)
    (F : Finset (Fin n)) :
    ∑ m ∈ F, idxWeight I m =
      ∑ c ∈ S, (if 1 ≤ c then (1 : ℤ) else -1) * ((F.filter fun m => m ∈ I c).card : ℤ) := by
  simp_rw [idxWeight_eq I S hS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m ∈ I c <;> simp [hm]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
