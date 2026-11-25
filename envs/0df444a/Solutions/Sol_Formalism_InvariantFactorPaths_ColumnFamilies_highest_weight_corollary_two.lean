-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:58.934488+00:00
-- url     : https://prove2.me/submissions/6d3d6b3a-66b6-47f3-9c17-95363443a4d8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_RationalBitableauLatticeStatement
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_bracket_mem_dualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_dualWeyl_le_span_bracket
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_eval_id_bracket_canonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_main
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_nu_anti
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_nu_cast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : RationalBitableauLatticeStatement := by
  intro n _ mu hmu
  have h := qn_main n (qn_nu mu) (qn_nu_anti hmu) (fun I : TIdx mu => brkPol mu I) (canT mu)
    (fun I => bracket_mem_dualWeyl hmu I) (dualWeyl_le_span_bracket hmu) (eval_id_bracket_canonical mu)
  rw [qn_nu_cast hmu] at h
  exact h
end Formalism.InvariantFactorPaths.ColumnFamilies
