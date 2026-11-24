-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.wMat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:04:51.742801+00:00
-- url     : https://prove2.me/submissions/449f2d63-8dd8-4896-bc30-c29f86fe2f27

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
theorem _root_.solution (n : ℕ) : (G.wMat n)ᴴ = G.wMat n := by
  ext a b
  simp only [Matrix.conjTranspose_apply, G.wMat, Matrix.of_apply]
  have h : (a = b.rev) ↔ (b = a.rev) := by
    constructor <;> rintro rfl <;> simp
  simp only [h]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Ux3
