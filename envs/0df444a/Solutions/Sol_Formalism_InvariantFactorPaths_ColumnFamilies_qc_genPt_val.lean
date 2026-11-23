-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_genPt_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:58.409812+00:00
-- url     : https://prove2.me/submissions/49c6ac48-1bf1-42ff-806f-1e72aaee88e4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (F : Type) [CommRing F] (n : ℕ) (a b : Fin n) :
    (qc_genPt F n).val a b = algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n) (X (a, b)) := rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
