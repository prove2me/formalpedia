-- Prove2me | solution 1 for BookProof.ChapterA3.lorentz_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:33:38.185307+00:00
-- url     : https://prove2.me/submissions/471aa6a8-6058-400c-8dc9-68572690c67e

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix
set_option maxHeartbeats 0

private lemma comb (a b : Fin 4 → ℂ) :
    (∑ k, a k • mgamma k) * (∑ k, b k • mgamma k) +
      (∑ k, b k • mgamma k) * (∑ k, a k • mgamma k) =
    (-2 * (a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3)) •
      (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, mgamma, mgammaZ, Matrix.mul_apply, Matrix.one_apply] <;> ring

private lemma metric_entry (Λ : Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    (Λ * minkowskiMat * Λᵀ) μ ν =
      Λ μ 0 * Λ ν 0 - Λ μ 1 * Λ ν 1 - Λ μ 2 * Λ ν 2 - Λ μ 3 * Λ ν 3 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiMat, minkowskiR, minkowskiZ]
  ring

private lemma clifford_local (μ ν : Fin 4) :
    mgamma μ * mgamma ν + mgamma ν * mgamma μ =
      (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hZ : mgammaZ μ * mgammaZ ν + mgammaZ ν * mgammaZ μ =
      (-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    fin_cases μ <;> fin_cases ν <;> decide
  have hscalar :
      (Int.castRingHom ℂ).mapMatrix ((-2 * minkowskiZ μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) =
        (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    ext i j
    simp [minkowski, Matrix.one_apply, Matrix.mul_apply,
      Matrix.intCast_apply, Matrix.natCast_apply, Matrix.ofNat_apply] <;>
      split_ifs <;> ring
  have hCast := congrArg (Int.castRingHom ℂ).mapMatrix hZ
  rw [(Int.castRingHom ℂ).mapMatrix.map_add,
    (Int.castRingHom ℂ).mapMatrix.map_mul,
    (Int.castRingHom ℂ).mapMatrix.map_mul] at hCast
  rw [hscalar] at hCast
  simpa [mgamma, minkowski] using hCast

private lemma conjugate_clifford (S : Matrix (Fin 4) (Fin 4) ℂ)
    (hS : IsUnit S.det) (μ ν : Fin 4) :
    (S⁻¹ * mgamma μ * S) * (S⁻¹ * mgamma ν * S) +
      (S⁻¹ * mgamma ν * S) * (S⁻¹ * mgamma μ * S) =
      (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hc : mgamma μ * mgamma ν + mgamma ν * mgamma μ =
      (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    exact clifford_local μ ν
  have hm (A B : Matrix (Fin 4) (Fin 4) ℂ) :
      (S⁻¹ * A * S) * (S⁻¹ * B * S) = S⁻¹ * (A * B) * S := by
    calc
      _ = S⁻¹ * A * (S * S⁻¹) * B * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hS]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hm, hm, ← Matrix.add_mul, ← Matrix.mul_add, hc]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hS]

theorem solution (S : Matrix (Fin 4) (Fin 4) ℂ) (hS : IsUnit S.det)
    (Lam : Matrix (Fin 4) (Fin 4) ℝ)
    (hLam : ∀ μ, S⁻¹ * mgamma μ * S = ∑ ν, (Lam μ ν : ℂ) • mgamma ν) :
    Lam * minkowskiMat * Lamᵀ = minkowskiMat := by
  ext μ ν
  have h := conjugate_clifford S hS μ ν
  rw [hLam μ, hLam ν, comb] at h
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at he
  have hr := congrArg Complex.re he
  simp [Complex.mul_re, minkowski, minkowskiR] at hr
  rw [metric_entry]
  change _ = minkowskiR μ ν
  unfold minkowskiR
  linarith
#print axioms solution
