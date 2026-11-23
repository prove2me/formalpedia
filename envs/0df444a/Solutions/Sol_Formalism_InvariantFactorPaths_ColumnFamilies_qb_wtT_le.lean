-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_wtT_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:49.032468+00:00
-- url     : https://prove2.me/submissions/2e6d6690-c611-4b4d-9c11-e0755e86412a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_sum_wtT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_col_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_can

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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) : DomLE (qb_wtT mu I) mu := by
  constructor
  · intro a
    conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    have : ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (I c).1)).card : ℤ) ≤
        ∑ c : ↥(TCols mu), (((univ.filter (· ≤ a)).filter (· ∈ (canT mu c).1)).card : ℤ) :=
      sum_le_sum fun c _ => by exact_mod_cast qb_col_le mu c (I c).1 (I c).2 a
    linarith
  · conv_rhs => rw [← qb_wtT_can hmu]
    rw [qb_sum_wtT, qb_sum_wtT]
    congr 1
    refine sum_congr rfl fun c _ => ?_
    simp only [filter_univ_mem]
    rw [(I c).2, (canT mu c).2]
end Formalism.InvariantFactorPaths.ColumnFamilies
