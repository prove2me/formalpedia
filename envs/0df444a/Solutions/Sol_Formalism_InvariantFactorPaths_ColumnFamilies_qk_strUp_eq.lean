-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_strUp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:24.749155+00:00
-- url     : https://prove2.me/submissions/de11f2d0-fc5c-49f4-aac1-cbf48b824a7d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ExtendedColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_hstrip_iff

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
theorem _root_.solution {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strUp mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp mu b := by
  unfold strUp Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsUp
  ext nu
  simp only [mem_filter, qk_hstrip_iff]
end Formalism.InvariantFactorPaths.ColumnFamilies
