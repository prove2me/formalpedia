-- Prove2me | solution 1 for BookProof.ChapterGammaCommutant.gamma_commutant_eq_scalars
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:22:47.432472+00:00
-- url     : https://prove2.me/submissions/aac904df-a154-444e-90bb-3af3d3712ba0

-- Generated from ChapterGammaCommutant.lean — solution of BookProof.ChapterGammaCommutant.gamma_commutant_eq_scalars
import Mathlib
import Definitions.Def_ChapterGammaCommutant
import Theorems.Thm_BookProof_ChapterGammaCommutant_gamma_commutant_scalar
open BookProof.ChapterGammaCommutant



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    {X : Matrix (Fin 4) (Fin 4) ℂ | ∀ μ, X * mgamma μ = mgamma μ * X}
      = {X | ∃ c : ℂ, X = c • (1 : Matrix (Fin 4) (Fin 4) ℂ)} := by

  ext X
  constructor
  · intro hX
    exact ⟨X 0 0, gamma_commutant_scalar X hX⟩
  · rintro ⟨c, rfl⟩ μ
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
