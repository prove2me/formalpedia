-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.wMat_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:15:55.00882+00:00
-- url     : https://prove2.me/submissions/8325d272-e231-432e-b19b-1668cfe5edf5

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_apply

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
theorem _root_.solution (n : ℕ) : G.wMat n * G.wMat n = 1 := by
  ext a b
  rw [wMat_mul_apply]
  by_cases h : a = b
  · subst h
    simp [G.wMat]
  · simp [G.wMat, Matrix.one_apply, h, Ne.symm h]
end Formalism.FourierDecayAlt.P.Ux3
