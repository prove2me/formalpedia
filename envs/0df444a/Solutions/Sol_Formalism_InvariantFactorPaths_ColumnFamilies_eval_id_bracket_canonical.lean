-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.eval_id_bracket_canonical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:51.414164+00:00
-- url     : https://prove2.me/submissions/b8cd51ec-3abc-41ca-8bd3-d0a559c17f75

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_T_brkPol
import Theorems.Thm_Formalism_GradedWeylDivisibility_eval_idPoint_lpMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_can_emb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    eval (idFrame ℤ n n) (transposeVariables ℤ n (brkPol mu (canT mu))) = 1 := by
  rw [qn_T_brkPol, map_mul, map_pow]
  have h1 : eval (idFrame ℤ n n) (qn_delta n) = 1 := eval_idPoint_lpMinor ℤ n (le_refl n) (le_refl n)
  rw [h1, one_pow, one_mul]
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_eq_one fun c _ => ?_
  have h2 : initMinor ℤ (qa_row (canT mu) c) (colH_le mu c) =
      lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c) := by
    unfold initMinor lpMinor
    congr 1
    ext p q
    simp [qa_row, qa_can_emb]
  rw [h2]
  exact eval_idPoint_lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c)
end Formalism.InvariantFactorPaths.ColumnFamilies
