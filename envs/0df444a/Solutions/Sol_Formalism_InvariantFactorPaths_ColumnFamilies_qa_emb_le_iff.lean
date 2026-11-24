-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qa_emb_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:41.934534+00:00
-- url     : https://prove2.me/submissions/e578ce1f-a33e-432c-9ccf-eabe192ba998

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Lemmata_GeneralBFactSecondTer_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaRowStrictMono
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_lower_iff

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
theorem _root_.solution {n h : ℕ} (J : Finset (Fin n)) (hJ : J.card = h) (p : Fin h) (a : Fin n) :
    J.orderEmbOfFin hJ p ≤ a ↔ p.val < (J.filter (· ≤ a)).card := by
  have h1 : (J.filter (· ≤ a)).card = (univ.filter fun q : Fin h => J.orderEmbOfFin hJ q ≤ a).card := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J hJ]
    rw [Finset.filter_map, Finset.card_map]
    rfl
  rw [h1]
  exact qa_lower_iff (fun q : Fin h => J.orderEmbOfFin hJ q ≤ a)
    (fun q q' hqq hq => ((J.orderEmbOfFin hJ).monotone hqq).trans hq) p
end Formalism.InvariantFactorPaths.ColumnFamilies
