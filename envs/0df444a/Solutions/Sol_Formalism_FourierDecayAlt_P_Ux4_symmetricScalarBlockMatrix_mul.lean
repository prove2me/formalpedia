-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.symmetricScalarBlockMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:39.415329+00:00
-- url     : https://prove2.me/submissions/27c1f4fc-4f8a-4ef3-89da-5f9b599b66c9

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
theorem _root_.solution {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
end Formalism.FourierDecayAlt.P.Ux4
