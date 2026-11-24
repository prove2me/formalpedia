-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.zhDmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:01.953554+00:00
-- url     : https://prove2.me/submissions/ca2015df-8ac2-4e0f-b8d0-4651b295d427

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_zhat_apply_low

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
theorem _root_.solution : ZhDmin := by
  intro k j ρ z z' g
  unfold Dmin DjU
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  rw [zhat_apply_low]
  · rfl
  · simp; omega
  · simp; omega
end Formalism.FourierDecayAlt.P.Ux3
