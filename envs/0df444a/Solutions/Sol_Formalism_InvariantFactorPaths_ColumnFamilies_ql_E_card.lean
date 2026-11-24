-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_E_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:24.752374+00:00
-- url     : https://prove2.me/submissions/c344ca87-438f-437d-904b-5de8c27e6327

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_card


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
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) (lo : ℤ) (N : ℕ) (I : TIdx mu) (j : Fin N) :
    (ql_E lo N (qs_ext mu I) j).card = colH mu (lo + 1 + (j : ℕ)) := qs_ext_card hmu I _
end Formalism.InvariantFactorPaths.ColumnFamilies
