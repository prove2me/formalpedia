-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.387408+00:00
-- url     : https://prove2.me/submissions/de17f5e8-955d-4249-accd-7850a1639770

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal

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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (ε : ℤ) (I : TIdx (qc_sh mu ε)) (c : ↥(TCols mu)) :
    (qc_idxE mu ε I c).1 = (I (qc_colE mu ε c)).1 := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
