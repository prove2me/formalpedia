-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.symmetric_power_count_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:24.439805+00:00
-- url     : https://prove2.me/submissions/9f5e53fa-3783-4688-85a9-68dd004150fb

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_hstrip_dom
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_strUp_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_mem_strUp
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
theorem _root_.solution : CntSym := by
  intro n _ mu b hmu
  rw [qk_card_symIdx, qk_dMu_eq_dGT n mu hmu, ← (Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.gtPieri n mu b hmu).1, ← qk_strUp_eq]
  refine sum_congr rfl fun nu hnu => ?_
  rw [qk_dMu_eq_dGT n nu (qk_hstrip_dom (qk_mem_strUp hnu)).2]
end Formalism.InvariantFactorPaths.ColumnFamilies
