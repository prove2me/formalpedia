-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block2_det_upper_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:35.875732+00:00
-- url     : https://prove2.me/submissions/63ec3c92-75c3-4406-8111-0c6e496da682

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    (blk2 A B 0 D).det = A.det * D.det := by
  rw [blk2, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
end Formalism.FourierDecayAlt.P.Ux4
