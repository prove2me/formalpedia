-- Prove2me | solution 1 for Diaz.Gmat_projection
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:41.772797+00:00
-- url     : https://prove2.me/submissions/5598669d-13cc-4cf5-9e0f-93fdc94d69a8

import Mathlib

open ComplexConjugate

theorem solution {u r : ℂ} (x y : ℝ) (hu : u = (x : ℂ) + (y : ℂ) * Complex.I)
    (hr : r ≠ 0) (h : u * conj u = r ^ 2) :
    (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]).det = 0
      ∧ Matrix.trace (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]) = 2 * r
      ∧ ((2 * r)⁻¹ • (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]))
          * ((2 * r)⁻¹ • (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]))
        = (2 * r)⁻¹ • (!![r + (x : ℂ), -(y : ℂ); -(y : ℂ), r - (x : ℂ)]) := by
  have hc : conj u = (x : ℂ) - (y : ℂ) * Complex.I := by
    rw [hu]; simp <;> ring
  have hx : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = r ^ 2 := by
    rw [hc, hu] at h
    linear_combination h + ((y : ℂ) ^ 2) * Complex.I_sq
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.of_apply]
    linear_combination -hx
  · rw [Matrix.trace_fin_two]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.of_apply]
    ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.of_apply,
        Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      field_simp <;> ring_nf <;> linear_combination hx
