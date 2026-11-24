-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_keyZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:50.203189+00:00
-- url     : https://prove2.me/submissions/3d909b04-747d-42ba-8aa7-0f4efd92c714

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_prMu_ph


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) (nu : Fin n → ℤ) (i : M.ι) :
    ∑ k, (prMu M nu i k : GLCoord ℤ n) * ∑ l, M.A k l * (CF.ph j l I : GLCoord ℤ n) =
      ∑ K, if qb_wtT (CF.mu j) K = nu then (CF.ph j i K : GLCoord ℤ n) * TMat (CF.mu j) K I else 0 := by
  simp only [qb_equiv_apply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun K _ => ?_
  have h2 := congrArg (Int.cast : ℤ → GLCoord ℤ n) (qb_prMu_ph CF j nu i K)
  push_cast at h2
  simp only [← mul_assoc, ← sum_mul]
  rw [h2]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.ColumnFamilies
