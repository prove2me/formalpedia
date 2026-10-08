-- Prove2me | solution 1 for BookProof.ChapterA3.lambdaOf_mul
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:25:07.34244+00:00
-- url     : https://prove2.me/submissions/e69adb82-93cd-4139-842d-ca1b91840f82

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix
set_option maxHeartbeats 0

private theorem mul_local {S₁ S₂ Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (_h1 : IsUnit S₁.det) (_h2 : IsUnit S₂.det)
    (hL1 : HasLambda S₁ Λ₁) (hL2 : HasLambda S₂ Λ₂) :
    HasLambda (S₁ * S₂) (Λ₁ * Λ₂) := by
  intro μ
  rw [Matrix.mul_inv_rev]
  calc
    S₂⁻¹ * S₁⁻¹ * mgammaR μ * (S₁ * S₂) =
        S₂⁻¹ * (S₁⁻¹ * mgammaR μ * S₁) * S₂ := by simp only [Matrix.mul_assoc]
    _ = S₂⁻¹ * (∑ ν, Λ₁ μ ν • mgammaR ν) * S₂ := by rw [hL1 μ]
    _ = ∑ ν, Λ₁ μ ν • (S₂⁻¹ * mgammaR ν * S₂) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = ∑ ν, Λ₁ μ ν • (∑ ρ, Λ₂ ν ρ • mgammaR ρ) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [hL2 ν]
    _ = ∑ ρ, (Λ₁ * Λ₂) μ ρ • mgammaR ρ := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]


private theorem pin_local {S₁ S₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : IsPin S₁) (h2 : IsPin S₂) : IsPin (S₁ * S₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact h1.1.mul h2.1
  · rw [Matrix.det_mul, abs_mul, h1.2.1, h2.2.1, one_mul]
  · obtain ⟨Λ₁, hL1⟩ := h1.2.2
    obtain ⟨Λ₂, hL2⟩ := h2.2.2
    exact ⟨Λ₁ * Λ₂, mul_local h1.1 h2.1 hL1 hL2⟩

private theorem unique_local {S Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ}
    (h : HasLambda S Λ) (h' : HasLambda S Λ') : Λ = Λ' := by
  ext μ ν
  have he := (h μ).symm.trans (h' μ)
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) he
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) he
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) he
  have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) he
  simp [Fin.sum_univ_four, mgammaR, mgammaZ, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply] at h00 h01 h02 h20
  fin_cases ν
  · change Λ μ 0 = Λ' μ 0
    linarith
  · exact h00
  · change Λ μ 2 = Λ' μ 2
    linarith
  · exact h01


private theorem choice_local (S : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S) := by
  classical
  simpa only [LambdaOf, dif_pos h] using h.choose_spec

theorem solution {S₁ S₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : IsPin S₁) (h2 : IsPin S₂) :
    LambdaOf (S₁ * S₂) = LambdaOf S₁ * LambdaOf S₂ := by
  exact unique_local (choice_local _ (pin_local h1 h2).2.2)
    (mul_local h1.1 h2.1 (choice_local _ h1.2.2) (choice_local _ h2.2.2))
#print axioms solution
