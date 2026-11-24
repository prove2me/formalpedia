-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.wMat_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:21:25.491135+00:00
-- url     : https://prove2.me/submissions/7cfb2f4a-6f8e-4191-8c8c-94b88d49819d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_mul_apply

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
theorem _root_.solution (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext a b
  rw [wMat_mul_apply]
  by_cases h : a = b
  · subst h; simp [G.wMat]
  · have h' : b ≠ a.rev.rev := by rw [Fin.rev_rev]; exact Ne.symm h
    simp [G.wMat, h, h'] <;> exact fun e => h e.symm
end Formalism.FourierDecayAlt.P.Ux2
