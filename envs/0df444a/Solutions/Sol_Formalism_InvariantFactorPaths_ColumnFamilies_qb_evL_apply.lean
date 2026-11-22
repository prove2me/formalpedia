-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_evL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:38.219908+00:00
-- url     : https://prove2.me/submissions/ab0dc2c5-44f8-4991-87cb-9f5fa1280258

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField

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
theorem _root_.solution (M : GLMod n) (F : Type) [CommRing F] (nu : Fin n → ℤ) (x : M.ι → F) :
    qb_evL M F nu x = qb_ev M F nu x := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
