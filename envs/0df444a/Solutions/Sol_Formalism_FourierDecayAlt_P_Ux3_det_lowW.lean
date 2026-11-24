-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.det_lowW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:52.684948+00:00
-- url     : https://prove2.me/submissions/72a822f1-59e1-4d86-82d9-464032b52d95

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
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : (lowW σ v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [lowW]
  · intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp [lowW, Matrix.one_apply, ne_of_lt hab', not_lt.mpr hab'.le]
end Formalism.FourierDecayAlt.P.Ux3
