-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.permutationMatrix_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:54:06.328332+00:00
-- url     : https://prove2.me/submissions/333909eb-5b8a-445e-bebe-842464e563ea

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_mul_wP_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_inv

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
    (wP σ * M * (wP σ)⁻¹) a b = M (σ a) (σ b) := by
  rw [permutationMatrix_inv, mul_wP_apply, permutationMatrix_mul_apply]; simp
end Formalism.FourierDecayAlt.P.Ux2
