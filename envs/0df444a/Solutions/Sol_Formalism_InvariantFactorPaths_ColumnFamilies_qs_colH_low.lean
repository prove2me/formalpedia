-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_colH_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:54.389625+00:00
-- url     : https://prove2.me/submissions/d4328c07-e72b-44e1-84f7-ccc1bd0a8968

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_le_lastIdx


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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) {c : ℤ} (hc : c ≤ mu (lastIdx n)) : colH mu c = n := by
  unfold colH
  rw [Finset.filter_true_of_mem (fun m _ => hc.trans (hmu (qb_le_lastIdx m)))]; simp
end Formalism.InvariantFactorPaths.ColumnFamilies
