-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.det_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:33:02.866398+00:00
-- url     : https://prove2.me/submissions/30ed4906-ad1c-493e-b2dd-e1e9b54e7d2b

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
theorem _root_.solution {p : ℕ} (u : G.UT p → ℂ) : (G.upper u).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [G.upper, G.strictUpper]
  · intro a b hab
    have hab' : b < a := hab
    have hne : a ≠ b := (ne_of_lt hab').symm
    have hnl : ¬ a < b := not_lt.mpr hab'.le
    simp [G.upper, G.strictUpper, Matrix.one_apply, hne, hnl]
end Formalism.FourierDecayAlt.P.Ux3
