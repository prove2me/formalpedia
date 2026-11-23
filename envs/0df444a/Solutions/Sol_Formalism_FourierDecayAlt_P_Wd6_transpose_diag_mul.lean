-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.transpose_diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:37.441799+00:00
-- url     : https://prove2.me/submissions/f64b6296-e84e-4d1c-81ad-13fb216915a6

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
    ((Matrix.diagonal fun _ => z) * M)ᵀ = (Matrix.diagonal fun _ => z) * Mᵀ := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.transpose_apply]
end Formalism.FourierDecayAlt.P.Wd6
