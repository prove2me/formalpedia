-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_row_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:13.25269+00:00
-- url     : https://prove2.me/submissions/90b03025-95b7-4341-addf-0aa54c8325e7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_emb_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) (c : ↥(TCols mu)) (q : Fin (colH mu c))
    (a : Fin n) : qa_row I c q ≤ a ↔ q.val < qa_cnt I c a := qa_emb_le_iff (I c).1 (I c).2 q a
end Formalism.InvariantFactorPaths.ColumnFamilies
