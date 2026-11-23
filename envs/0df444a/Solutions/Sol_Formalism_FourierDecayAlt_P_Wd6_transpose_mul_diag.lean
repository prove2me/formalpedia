-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.transpose_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:37.640538+00:00
-- url     : https://prove2.me/submissions/b11ed4d9-b713-44ff-929f-d16ad609d34f

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (M : M2 B) (z : B) :
    (M * (Matrix.diagonal fun _ => z))ᵀ = Mᵀ * (Matrix.diagonal fun _ => z) := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.transpose_apply]
end Formalism.FourierDecayAlt.P.Wd6
