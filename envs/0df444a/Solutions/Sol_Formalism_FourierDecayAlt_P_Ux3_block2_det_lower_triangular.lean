-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.block2_det_lower_triangular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:16.280807+00:00
-- url     : https://prove2.me/submissions/d255f26e-b092-4886-815b-abf9b643b4fd

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
theorem _root_.solution {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : (blk2 A 0 C D).det = A.det * D.det := by
  simp only [blk2]
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]
end Formalism.FourierDecayAlt.P.Ux3
