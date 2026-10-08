-- Prove2me | solution 1 for BookProof.ChapterA3.cliffordR_lorentz_comb
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:26:22.780078+00:00
-- url     : https://prove2.me/submissions/523288ff-90af-444a-bfa3-50ec2fed24a0

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix
set_option maxHeartbeats 0

private lemma comb (a b : Fin 4 → ℝ) :
    (∑ k, a k • mgammaR k) * (∑ k, b k • mgammaR k) +
      (∑ k, b k • mgammaR k) * (∑ k, a k • mgammaR k) =
    (-2 * (a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3)) •
      (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, mgammaR, mgammaZ, Matrix.mul_apply, Matrix.one_apply] <;> ring

private lemma metric_entry (Λ : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    (Λ * minkowskiMat * Λᵀ) μ ν =
      Λ μ 0 * Λ ν 0 - Λ μ 1 * Λ ν 1 - Λ μ 2 * Λ ν 2 - Λ μ 3 * Λ ν 3 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMat, minkowskiR, minkowskiZ]
  ring

theorem solution (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) :
    IsCliffordR (fun μ => ∑ ν, Λ μ ν • mgammaR ν) := by
  intro μ ν
  rw [comb]
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M μ ν) hΛ
  rw [metric_entry] at he
  change _ = minkowskiR μ ν at he
  rw [he]

#print axioms solution

