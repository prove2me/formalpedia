-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_strDown_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:24.726487+00:00
-- url     : https://prove2.me/submissions/1e5f3369-23d8-4c79-bc55-1833f44759f3

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
theorem _root_.solution {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : strDown mu b = Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown mu b := by
  unfold strDown Formalism.InvariantFactorPaths.GelfandTsetlinBases.stripsDown
  ext nu
  simp only [mem_filter, qk_hstrip_iff]
end Formalism.InvariantFactorPaths.ColumnFamilies
