-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.block2_det_upper_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:49.563473+00:00
-- url     : https://prove2.me/submissions/c7e49c80-6ec7-419a-b547-0e9c5ab9b2f5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A B 0 D).det = A.det * D.det := by
  simp only [blk2]
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
end Formalism.FourierDecayAlt.P.Ux3
