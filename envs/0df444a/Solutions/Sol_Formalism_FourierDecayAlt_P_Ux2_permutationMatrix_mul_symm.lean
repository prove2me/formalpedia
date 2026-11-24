-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.permutationMatrix_mul_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:15:50.885236+00:00
-- url     : https://prove2.me/submissions/7d583ec6-dbdb-4783-b6d0-e25f631828c9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_mul_apply

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
theorem _root_.solution (σ : Equiv.Perm (Fin p)) : wP σ * wP σ.symm = 1 := by
  ext a b
  rw [permutationMatrix_mul_apply]
  by_cases h : a = b
  · subst h; simp [wP]
  · simp [wP, Matrix.one_apply_ne h, h]
end Formalism.FourierDecayAlt.P.Ux2
