-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:26:00.405983+00:00
-- url     : https://prove2.me/submissions/cb0d6d61-5583-4d77-904b-5dc5f043eaae

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
theorem _root_.solution {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a : Fin n) :
    skewOf q a a = Complex.I * (q.2 a : ℂ) := by
  simp [skewOf, G.strictUpper]
end Formalism.FourierDecayAlt.P.Ux3
