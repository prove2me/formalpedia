-- Prove2me | solution 1 for BookProof.ChapterA3.lambda_mem_lorentz
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:32:09.928609+00:00
-- url     : https://prove2.me/submissions/5f712bcb-f817-4a28-a7d8-167fd2b42532

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

private lemma clifford_local (μ ν : Fin 4) :
    mgammaR μ * mgammaR ν + mgammaR ν * mgammaR μ =
      (-2 * minkowskiR μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hZ : mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ =
      (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    fin_cases μ <;> fin_cases ν <;> decide
  have hscalar :
      (Int.castRingHom ℝ).mapMatrix ((-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) =
        (-2 * minkowskiR μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    simp [minkowskiR, Matrix.one_apply, Matrix.mul_apply,
      Matrix.intCast_apply, Matrix.natCast_apply, Matrix.ofNat_apply] <;>
      split_ifs <;> ring
  have hCast := congrArg (Int.castRingHom ℝ).mapMatrix hZ
  rw [(Int.castRingHom ℝ).mapMatrix.map_add,
    (Int.castRingHom ℝ).mapMatrix.map_mul,
    (Int.castRingHom ℝ).mapMatrix.map_mul] at hCast
  rw [hscalar] at hCast
  simpa [mgammaR, minkowskiR] using hCast

private lemma conjugate_clifford (S : Matrix (Fin 4) (Fin 4) ℝ)
    (hS : IsUnit S.det) (μ ν : Fin 4) :
    (S⁻¹ * mgammaR μ * S) * (S⁻¹ * mgammaR ν * S) +
      (S⁻¹ * mgammaR ν * S) * (S⁻¹ * mgammaR μ * S) =
      (-2 * minkowskiR μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  have hc : mgammaR μ * mgammaR ν + mgammaR ν * mgammaR μ =
      (-2 * minkowskiR μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    exact clifford_local μ ν
  have hm (A B : Matrix (Fin 4) (Fin 4) ℝ) :
      (S⁻¹ * A * S) * (S⁻¹ * B * S) = S⁻¹ * (A * B) * S := by
    calc
      _ = S⁻¹ * A * (S * S⁻¹) * B * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hS]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hm, hm, ← Matrix.add_mul, ← Matrix.mul_add, hc]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hS]

private lemma lorentz_local (S : Matrix (Fin 4) (Fin 4) ℝ)
    (hS : IsUnit S.det) (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : HasLambda S Λ) :
    Λ * minkowskiMat * Λᵀ = minkowskiMat := by
  ext μ ν
  have h := conjugate_clifford S hS μ ν
  rw [hΛ μ, hΛ ν, comb] at h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at he
  rw [metric_entry]
  change _ = minkowskiR μ ν
  linarith

private theorem choice_local (S : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S) := by
  classical
  simpa only [LambdaOf, dif_pos h] using h.choose_spec

theorem solution (S : Matrix (Fin 4) (Fin 4) ℝ) (hS : IsPin S) :
    LambdaOf S ∈ LorentzO := lorentz_local S hS.1 _ (choice_local S hS.2.2)
#print axioms solution
