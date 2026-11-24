-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:42:22.803599+00:00
-- url     : https://prove2.me/submissions/638ac9fb-95ce-48ed-88ea-c7f07fadff10

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
theorem _root_.solution {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a b : Fin n) (h : a < b) :
    skewOf q a b = q.1 ⟨(a, b), h⟩ := by
  simp [skewOf, G.strictUpper, h, not_lt.mpr h.le, ne_of_lt h]
end Formalism.FourierDecayAlt.P.Ux3
