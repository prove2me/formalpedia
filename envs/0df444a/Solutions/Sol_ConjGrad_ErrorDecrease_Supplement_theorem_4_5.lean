-- Prove2me | solution 1 for ConjGrad.ErrorDecrease.Supplement.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T09:11:55.252583+00:00
-- url     : https://prove2.me/submissions/c1000f90-6535-45f0-b362-fc1265e6f666

import Mathlib

open Matrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (p : Fin n → Fin n → ℝ) (hp : ∀ i, p i ≠ 0)
    (hconj : ∀ i j, i ≠ j → p i ⬝ᵥ (A *ᵥ p j) = 0) (j l : Fin n) :
    A⁻¹ j l = ∑ i, p i j * p i l / (p i ⬝ᵥ (A *ᵥ p i)) := by
  classical
  let P : Matrix (Fin n) (Fin n) ℝ := p
  let d : Fin n → ℝ := fun i => p i ⬝ᵥ (A *ᵥ p i)
  have hdpos : ∀ i, 0 < d i := by
    intro i
    have := hA.dotProduct_mulVec_pos (hp i)
    simpa [d] using this
  have hdne : ∀ i, d i ≠ 0 := fun i => ne_of_gt (hdpos i)
  -- Conjugacy says P * A * Pᵀ is diagonal with entries d i.
  have hentry : ∀ i j, (P * A * P.transpose) i j = P i ⬝ᵥ (A *ᵥ P j) := by
    intro i j
    rw [mul_assoc]
    simp only [mul_apply, transpose_apply, mulVec, dotProduct]
  have hPAPt : P * A * P.transpose = diagonal d := by
    ext i j
    rw [hentry]
    by_cases hij : i = j
    · subst hij
      simp [d, P]
    · rw [diagonal_apply_ne d hij]
      exact hconj i j hij
  -- P is invertible: det(P)^2 * det(A) = ∏ d i ≠ 0.
  have hpunit : IsUnit P := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    have hdet : P.det * A.det * P.det = ∏ i, d i := by
      have := congr_arg Matrix.det hPAPt
      simpa [det_mul, det_transpose, det_diagonal] using this
    have hprod : ∏ i, d i ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hdne i)
    intro hp0
    have h0 : ∏ i, d i = 0 := by rw [← hdet, hp0]; ring
    exact hprod h0
  have hDunit : IsUnit (diagonal d) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdne i)
  letI := hpunit.invertible
  letI := hDunit.invertible
  -- A * (Pᵀ * D⁻¹ * P) = 1, hence A⁻¹ = Pᵀ * D⁻¹ * P.
  have h1 : A * P.transpose = P⁻¹ * diagonal d := by
    have := congr_arg (fun M => P⁻¹ * M) hPAPt
    simpa [mul_assoc, inv_mul_of_invertible] using this
  have h2 : A * (P.transpose * (diagonal d)⁻¹ * P) = 1 := by
    calc A * (P.transpose * (diagonal d)⁻¹ * P)
        = (A * P.transpose) * (diagonal d)⁻¹ * P := by simp [mul_assoc]
      _ = (P⁻¹ * diagonal d) * (diagonal d)⁻¹ * P := by rw [h1]
      _ = P⁻¹ * (diagonal d * (diagonal d)⁻¹) * P := by simp [mul_assoc]
      _ = P⁻¹ * 1 * P := by rw [mul_inv_of_invertible (diagonal d)]
      _ = 1 := by simp [inv_mul_of_invertible]
  have hinv : A⁻¹ = P.transpose * (diagonal d)⁻¹ * P := inv_eq_right_inv h2
  have hjl : A⁻¹ j l = (P.transpose * (diagonal d)⁻¹ * P) j l :=
    congr_fun (congr_fun hinv j) l
  -- Entry-wise, D⁻¹ is the diagonal of reciprocals.
  have hDinv : (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
    apply inv_eq_right_inv
    have hfun : (fun i => d i * (d i)⁻¹) = (1 : Fin n → ℝ) := by
      ext i
      exact mul_inv_cancel₀ (hdne i)
    rw [diagonal_mul_diagonal, hfun, diagonal_one']
  rw [hjl, hDinv, mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_diagonal, transpose_apply]
  simp only [P, d]
  rw [div_eq_mul_inv]
  ring
