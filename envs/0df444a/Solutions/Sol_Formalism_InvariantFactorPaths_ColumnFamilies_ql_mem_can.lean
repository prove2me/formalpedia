-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:54.380129+00:00
-- url     : https://prove2.me/submissions/d84d43c2-8c6c-440b-ad41-1626ef9be6a7

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_lt_colH_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_can


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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (a : Fin n) :
    a ∈ qs_ext mu (canT mu) c ↔ c ≤ mu a := by
  rw [qs_ext_can hmu, ← qb_lt_colH_iff hmu]; simp [qs_ini]
end Formalism.InvariantFactorPaths.ColumnFamilies
