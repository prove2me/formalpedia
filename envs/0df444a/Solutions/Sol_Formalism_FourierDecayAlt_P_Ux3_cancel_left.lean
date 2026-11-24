-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.cancel_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:15.769186+00:00
-- url     : https://prove2.me/submissions/8fcad890-0076-480d-96f7-bf0d6e12a075

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
theorem _root_.solution {m : Type*} {n : ℕ} (X : Matrix (Fin n) m ℂ) (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det)
    (h : W * X = 0) : X = 0 := by
  calc X = W⁻¹ * (W * X) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hW, Matrix.one_mul]
    _ = 0 := by rw [h, Matrix.mul_zero]
end Formalism.FourierDecayAlt.P.Ux3
