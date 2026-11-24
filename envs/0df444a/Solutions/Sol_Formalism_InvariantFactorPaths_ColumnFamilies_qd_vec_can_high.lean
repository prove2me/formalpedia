-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_vec_can_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:28:57.186914+00:00
-- url     : https://prove2.me/submissions/7be7802f-a2ab-44e1-b9eb-44baccebdd3e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_unipotent_eval_canonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_prMu_ph
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_can
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (j : CF.J) :
    IsHighest M R (CF.mu j) (fun i => (CF.vec j (canT (CF.mu j)) i : R)) := by
  constructor
  · funext i
    have := congrArg (Int.cast : ℤ → R) (qb_prMu_ph CF j (CF.mu j) i (canT (CF.mu j)))
    rw [if_pos (qb_wtT_can (CF.dom j))] at this
    push_cast at this
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using this
  · intro R' _ _ u h1 h2
    funext i
    have h := congrArg (evGL u) (qb_equiv_apply CF j i (canT (CF.mu j)))
    simp only [map_sum, map_mul, map_intCast, unipotent_eval_canonical u h1 h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    simpa [Matrix.mulVec, dotProduct, ColFam.vec] using h
end Formalism.InvariantFactorPaths.ColumnFamilies
