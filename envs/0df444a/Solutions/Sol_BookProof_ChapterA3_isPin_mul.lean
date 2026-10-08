-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_mul
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:25:04.978638+00:00
-- url     : https://prove2.me/submissions/78ba4c67-0c64-4d50-a69d-211d4b723520

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

theorem solution {S₁ S₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : IsPin S₁) (h2 : IsPin S₂) : IsPin (S₁ * S₂) := pin_local h1 h2
#print axioms solution
