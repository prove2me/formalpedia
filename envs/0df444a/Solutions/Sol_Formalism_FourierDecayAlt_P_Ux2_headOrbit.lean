-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.headOrbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:11.631016+00:00
-- url     : https://prove2.me/submissions/ac2954df-ec93-486a-a3a7-bab26fd9570e

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kS_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kS_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lower_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_uniK_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_mul_wP_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_mul_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_symm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_conj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowWSpec
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_uni
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_headH_inj

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
theorem _root_.solution : HeadOrbit := by
  intro p σ d hd
  refine ⟨fun l u hl hu => ?_, fun q => ?_⟩
  · rw [lower_iff] at hl
    rw [upper_iff] at hu
    have hc : ∀ a b, (wP σ.symm * l * wP σ) a b = l (σ.symm a) (σ.symm b) := by
      intro a b; rw [mul_wP_apply, permutationMatrix_mul_apply]
    have hm : uniK (kS σ) (wP σ.symm * l * wP σ) :=
      ⟨fun i => by rw [hc, hl.1], fun a b hab => by rw [hc]; exact hl.2 _ _ (kL_lt.mpr ((kS_lt σ).mp hab))⟩
    obtain ⟨L, N, hLk, hLl, hNu, hmLN⟩ := factor (kS_inj σ) _ hm
    obtain ⟨v, hv⟩ : ∃ v, L = lowW σ v := by
      apply (lowWSpec p σ L).mp
      refine ⟨(lower_iff L).mpr hLl, (lower_iff _).mpr ⟨fun i => by rw [permutationMatrix_conj_apply, hLk.1], fun a b hab => ?_⟩⟩
      rw [permutationMatrix_conj_apply]
      exact hLk.2 _ _ ((kS_lt σ).mpr (by simpa using kL_lt.mp hab))
    have hconj : uniK (kU p) (diagonal (fun i => (d i)⁻¹) * N * diagonal d) := by
      refine ⟨fun i => ?_, fun a b hab => ?_⟩
      · rw [mul_diagonal, diagonal_mul, hNu.1]; field_simp [hd i]
      · rw [mul_diagonal, diagonal_mul, hNu.2 a b hab]; simp
    have hU' := uniK_mul kU_inj hconj hu
    have hl' : l * wP σ = wP σ * (L * N) := by
      rw [← hmLN]; simp only [← Matrix.mul_assoc, permutationMatrix_mul_symm, Matrix.one_mul]
    have hdd : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i)
    have hex : l * hMat σ d * u = headH σ d v (fun q => (diagonal (fun i => (d i)⁻¹) * N * diagonal d * u) q.1.1 q.1.2) := by
      unfold headH hMat
      rw [← upper_eq hU', ← hv]
      calc l * (wP σ * diagonal d) * u = (l * wP σ) * diagonal d * u := by simp [Matrix.mul_assoc]
        _ = wP σ * (L * N) * diagonal d * u := by rw [hl']
        _ = wP σ * L * diagonal d * (diagonal (fun i => (d i)⁻¹) * N * diagonal d * u) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (diagonal d) (diagonal _), hdd, Matrix.one_mul]
    refine ⟨(v, fun q => (diagonal (fun i => (d i)⁻¹) * N * diagonal d * u) q.1.1 q.1.2), hex, fun y hy => ?_⟩
    obtain ⟨e1, e2⟩ := headH_inj σ d hd (hy.symm.trans hex)
    exact Prod.ext e1 e2
  · refine ⟨wP σ * lowW σ q.1 * (wP σ)⁻¹, G.upper q.2, ((lowWSpec p σ _).mpr ⟨q.1, rfl⟩).2,
      (upper_iff _).mpr (upper_uni q.2), ?_⟩
    rw [permutationMatrix_inv]
    simp only [hMat, headH, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (wP σ.symm) (wP σ), permutationMatrix_symm_mul, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.Ux2
