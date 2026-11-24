-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.headH_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:05.84132+00:00
-- url     : https://prove2.me/submissions/ddcc2e58-58cd-4e93-ab59-86274cd78e80

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_symm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_uni
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowW_uni
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowW_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lu_unique

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
theorem _root_.solution (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) {v1 v2 : LW σ → ℂ}
    {u1 u2 : G.UT p → ℂ} (h : headH σ d v1 u1 = headH σ d v2 u2) : v1 = v2 ∧ u1 = u2 := by
  have h' := congrArg (wP σ.symm * ·) h
  simp only [headH, Matrix.mul_assoc] at h'
  rw [← Matrix.mul_assoc (wP σ.symm), ← Matrix.mul_assoc (wP σ.symm), permutationMatrix_symm_mul, Matrix.one_mul,
    Matrix.one_mul] at h'
  simp only [← Matrix.mul_assoc] at h'
  obtain ⟨e1, e2⟩ := lu_unique d hd (lowW_uni σ v1) (lowW_uni σ v2) (upper_uni u1) (upper_uni u2) h'
  exact ⟨lowW_inj σ e1, upper_inj e2⟩
end Formalism.FourierDecayAlt.P.Ux2
