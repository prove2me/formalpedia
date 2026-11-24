-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.symmetricScalarBlockMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:54.441819+00:00
-- url     : https://prove2.me/submissions/d817716e-a4fd-430f-a121-443dce23d961

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p s : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D * blk2 A' B' C' D' = blk2 (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blk2
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
end Formalism.FourierDecayAlt.P.Ux2
