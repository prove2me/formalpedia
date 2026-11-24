-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.detZj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:54:02.808897+00:00
-- url     : https://prove2.me/submissions/0fc8461f-6fb6-4251-989b-1c48b279a894

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block2_det_lower_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block2_det_upper_triangular
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_det_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_det_lowW

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
theorem _root_.solution : DetZj := by
  intro p s σ d η Z
  unfold ZjH Zj headH hMat G.detM
  rw [Matrix.det_mul, Matrix.det_mul, block2_det_lower_triangular, block2_det_lower_triangular, block2_det_upper_triangular]
  simp only [Matrix.det_mul, det_upper, det_lowW, Matrix.det_one]
  ring
end Formalism.FourierDecayAlt.P.Ux3
