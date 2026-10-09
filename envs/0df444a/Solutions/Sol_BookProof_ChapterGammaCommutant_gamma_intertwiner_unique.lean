-- Prove2me | solution 1 for BookProof.ChapterGammaCommutant.gamma_intertwiner_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:23:12.546+00:00
-- url     : https://prove2.me/submissions/370ef675-de7a-4210-8d1b-788fcb23f08d

-- Generated from ChapterGammaCommutant.lean — solution of BookProof.ChapterGammaCommutant.gamma_intertwiner_unique
import Mathlib
import Definitions.Def_ChapterGammaCommutant
import Theorems.Thm_BookProof_ChapterGammaCommutant_gamma_commutant_scalar
open BookProof.ChapterGammaCommutant



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (S T : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det)
    (hSg : ∀ μ, S * mgamma μ = mgamma μ * S) (hTg : ∀ μ, T * mgamma μ = mgamma μ * T) :
    ∃ c : ℂ, T = c • S := by

  obtain ⟨cS, hcS⟩ : ∃ c : ℂ, S = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
    ⟨S 0 0, gamma_commutant_scalar S hSg⟩
  obtain ⟨cT, hcT⟩ : ∃ c : ℂ, T = c • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
    ⟨T 0 0, gamma_commutant_scalar T hTg⟩
  have hcS0 : cS ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcS
    subst hcS
    rw [Matrix.det_zero] at hS
    exact absurd hS not_isUnit_zero
  refine ⟨cT / cS, ?_⟩
  rw [hcT, hcS, smul_smul, div_mul_cancel₀ _ hcS0]
