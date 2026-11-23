-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.diag_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:39.040186+00:00
-- url     : https://prove2.me/submissions/57746d77-2367-4614-a67c-ce640b2a4365

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
theorem _root_.solution {z : B} {M : M2 B} (h : EC z M) :
    (Matrix.diagonal fun _ => z) * M = M * (Matrix.diagonal fun _ => z) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq
end Formalism.FourierDecayAlt.P.Wd6
