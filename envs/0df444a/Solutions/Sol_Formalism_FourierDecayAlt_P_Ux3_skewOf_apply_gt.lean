-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:31:02.796156+00:00
-- url     : https://prove2.me/submissions/4782d355-b5c1-4d93-ad91-42eb44261794

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
theorem _root_.solution {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a b : Fin n) (h : b < a) :
    skewOf q a b = -star (q.1 ⟨(b, a), h⟩) := by
  simp [skewOf, G.strictUpper, h, not_lt.mpr h.le, (ne_of_lt h).symm]
end Formalism.FourierDecayAlt.P.Ux3
