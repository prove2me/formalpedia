-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.dual_symmetric_power_count_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:22.351799+00:00
-- url     : https://prove2.me/submissions/8511cdb9-a92c-4889-9c96-2a25ff8cf419

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_hstrip_dom
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_strDown_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_mem_strDown
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_card_symIdx
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_dMu_eq_dGT
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_gtPieri


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : CntSymD := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).2, ← qk_strDown_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strDown hnu)).1]
end Formalism.InvariantFactorPaths.ColumnFamilies
