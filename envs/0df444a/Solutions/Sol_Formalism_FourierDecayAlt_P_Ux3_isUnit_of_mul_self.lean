-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.isUnit_of_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:01:58.641611+00:00
-- url     : https://prove2.me/submissions/71aec438-4f6d-4da0-b1d0-ebe12bb0f1db

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
theorem _root_.solution {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (h : W * W = 1) : IsUnit W.det := by
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  exact ⟨⟨W.det, W.det, h2, h2⟩, rfl⟩
end Formalism.FourierDecayAlt.P.Ux3
