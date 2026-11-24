-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_sU_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.243919+00:00
-- url     : https://prove2.me/submissions/ea5d306c-13d9-400d-9bcb-264d19a12a74

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (w : Fin n → ℤ) : ((qb_sU w : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) : AddMonoidAlgebra ℤ (Fin n → ℤ)) =
    AddMonoidAlgebra.single w 1 := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
