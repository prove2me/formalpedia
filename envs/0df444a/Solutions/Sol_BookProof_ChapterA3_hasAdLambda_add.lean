-- Prove2me | solution 1 for BookProof.ChapterA3.hasAdLambda_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:06:42.564898+00:00
-- url     : https://prove2.me/submissions/f865f327-9bee-45d8-93fb-f4ec06a45dc5

-- Generated from ChapterA3e.lean — solution of BookProof.ChapterA3.hasAdLambda_add
import Mathlib
import Definitions.Def_ChapterA3e
open BookProof.ChapterA3



open Matrix

set_option maxHeartbeats 1000000 in
theorem solution {G₁ G₂ A₁ A₂ : Matrix (Fin 4) (Fin 4) ℝ}
    (h1 : HasAdLambda G₁ A₁) (h2 : HasAdLambda G₂ A₂) :
    HasAdLambda (G₁ + G₂) (A₁ + A₂) := by

  intro μ
  have := h1 μ
  have := h2 μ
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
  rw [show ∑ ν, (A₁ μ ν + A₂ μ ν) • mgammaR ν
        = (∑ ν, A₁ μ ν • mgammaR ν) + ∑ ν, A₂ μ ν • mgammaR ν from ?_]
  · rw [← h1 μ, ← h2 μ]; abel
  · rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ν _ => by rw [add_smul]
