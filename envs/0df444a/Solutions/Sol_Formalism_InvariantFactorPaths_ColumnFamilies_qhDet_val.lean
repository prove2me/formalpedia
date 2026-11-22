-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qhDet_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:53.083709+00:00
-- url     : https://prove2.me/submissions/13ac5fa6-a096-43be-a58a-23ca258de853

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem

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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) = algebraMap _ _ (genMat R n).det := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
