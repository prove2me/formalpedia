-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_genMat_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.172955+00:00
-- url     : https://prove2.me/submissions/5d685c8e-918c-4d15-a453-103d7bded418

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
theorem _root_.solution (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genMat R n).det ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero (Fin n) R
end Formalism.InvariantFactorPaths.ColumnFamilies
