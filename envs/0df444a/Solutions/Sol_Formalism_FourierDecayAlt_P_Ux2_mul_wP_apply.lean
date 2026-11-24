-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.mul_wP_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:14.650412+00:00
-- url     : https://prove2.me/submissions/56d2c4b7-a1a3-4159-8839-7c07bd7a6f67

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
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (M * wP σ) a b = M a (σ.symm b) := by
  simp [wP, Matrix.mul_apply, ← Equiv.eq_symm_apply]
end Formalism.FourierDecayAlt.P.Ux2
