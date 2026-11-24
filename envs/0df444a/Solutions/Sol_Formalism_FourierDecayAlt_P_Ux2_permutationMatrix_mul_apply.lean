-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.permutationMatrix_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:53:44.814747+00:00
-- url     : https://prove2.me/submissions/76d1f8b9-faaa-4dab-a621-f59a58be1824

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
    (wP σ * M) a b = M (σ a) b := by
  simp [wP, Matrix.mul_apply]
end Formalism.FourierDecayAlt.P.Ux2
