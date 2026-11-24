-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rset_sub_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:08.941784+00:00
-- url     : https://prove2.me/submissions/6ca3678a-2ab0-40c3-b2d2-5311e0cbe889

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_sq_assoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rset_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_diag
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


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
theorem _root_.solution {g : B.Mat k (j + ρ)} (hg : g ∈ Rset k j ρ) : ∃ x, Rn k j ρ x = g := by
  obtain ⟨h11, h21, h31, h22, h32⟩ := rset_blocks hg
  have hH : (Hpk k ρ)ᴴ = Hpk k ρ := (hpkFacts k ρ).1
  have hG : gᴴ * Hpk k (j + ρ) * g = Hpk k (j + ρ) := hg.1
  have hgeta := block3_eta g
  rw [h11, h21, h31, h22, h32] at hgeta
  rw [hgeta, hpkBlocks k j ρ, block3_conjTranspose, block3_mul, block3_mul] at hG
  obtain ⟨-, -, e13, -, -, e23, -, -, e33⟩ := block3_injective hG
  simp [Matrix.mul_assoc, wMat_ct] at e13 e23 e33
  have hD : b33 g = 1 := by
    have := congrArg (G.wMat j * ·) e13
    simpa [wMat_sq_assoc, wMat_sq] using this
  rw [hD] at e23 e33 hgeta
  simp at e23 e33
  have hA1 : (b12 g)ᴴ * G.wMat j = -(Hpk k ρ * b23 g) := eq_neg_of_add_eq_zero_right e23
  have hA2 : (b12 g)ᴴ = -(Hpk k ρ * b23 g * G.wMat j) := by
    have := congrArg (· * G.wMat j) hA1
    simpa [Matrix.mul_assoc, wMat_sq] using this
  have hA : b12 g = -(G.wMat j * (b23 g)ᴴ * Hpk k ρ) := by
    have := congrArg Matrix.conjTranspose hA2
    simpa [Matrix.mul_assoc, wMat_ct, hH] using this
  set S : Matrix (Fin j) (Fin j) ℂ := G.wMat j * b13 g + (1 / 2 : ℂ) • ((b23 g)ᴴ * Hpk k ρ * b23 g) with hSdef
  have hS : Sᴴ = -S := by
    rw [eq_neg_iff_add_eq_zero, hSdef]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_smul, wMat_ct, hH, conjTranspose_conjTranspose]
    have hstar : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [hstar]
    rw [← e33]; simp only [Matrix.mul_assoc]; module
  have hSe : ∀ a b, star (S b a) = -S a b := fun a b => by
    have := congrFun (congrFun hS a) b
    simpa [conjTranspose_apply] using this
  let q : (G.UT j → ℂ) × (Fin j → ℝ) := (fun p => S p.1.1 p.1.2, fun a => (S a a).im)
  have hq : skewOf q = S := by
    ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [skewOf_lt _ h]
    · subst h
      rw [skewOf_diag]
      have hre : (S a a).re = 0 := by
        have := congrArg Complex.re (hSe a a)
        simp at this; linarith
      apply Complex.ext <;> simp [q, hre]
    · have h1 := congrFun (congrFun (skewOf_ct q) a) b
      simp only [conjTranspose_apply, Matrix.neg_apply] at h1
      rw [skewOf_lt _ h] at h1
      have h2 := hSe a b
      exact neg_inj.mp (h1.symm.trans h2)
  refine ⟨(Matrix.of.symm (b23 g), q), ?_⟩
  conv_rhs => rw [hgeta]
  unfold Rn
  refine block3_congr rfl ?_ ?_ rfl rfl ?_ rfl rfl rfl
  · simp [hA]
  · rw [hq, hSdef]
    simp only [Equiv.apply_symm_apply]
    have : (-(1 / 2 : ℂ)) • ((b23 g)ᴴ * Hpk k ρ * b23 g) +
        (G.wMat j * b13 g + (1 / 2 : ℂ) • ((b23 g)ᴴ * Hpk k ρ * b23 g)) = G.wMat j * b13 g := by module
    rw [this, wMat_sq_assoc]
  · simp
end Formalism.FourierDecayAlt.P.Ux2
