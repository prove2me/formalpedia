-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.skewOf_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:55:16.396827+00:00
-- url     : https://prove2.me/submissions/5f9d0cef-6c9b-4d52-9fc5-798edcbfae43

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
theorem _root_.solution (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by
  ext a b
  by_cases h : a = b
  · subst h; simp [skewOf, G.strictUpper, conjTranspose_apply]
  · simp [skewOf, conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]
end Formalism.FourierDecayAlt.P.Ux2
