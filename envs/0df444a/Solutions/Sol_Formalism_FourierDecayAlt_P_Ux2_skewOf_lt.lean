-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.skewOf_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:28.033825+00:00
-- url     : https://prove2.me/submissions/6acce72b-db7e-41f8-876a-6a262e475756

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (q : (G.UT j → ℂ) × (Fin j → ℝ)) {a b : Fin j} (h : a < b) : skewOf q a b = q.1 ⟨(a, b), h⟩ := by
  simp [skewOf, G.strictUpper, h, not_lt.mpr h.le, ne_of_lt h, conjTranspose_apply]
end Formalism.FourierDecayAlt.P.Ux2
