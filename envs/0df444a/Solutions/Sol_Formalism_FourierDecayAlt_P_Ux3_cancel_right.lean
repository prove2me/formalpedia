-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.cancel_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:30:58.073969+00:00
-- url     : https://prove2.me/submissions/e1234fb0-5431-453d-9a1c-f180d2884eb5

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
theorem _root_.solution {m : Type*} {n : ℕ} (X : Matrix m (Fin n) ℂ) (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det)
    (h : X * W = 0) : X = 0 := by
  calc X = X * W * W⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hW, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.Ux3
