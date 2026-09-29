-- Prove2me | solution 2 for Diaz.Gmat_projection
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:20:59.118979+00:00
-- url     : https://prove2.me/submissions/ea28702a-537d-4ad5-869d-1ca359ae803f

/-
`Diaz.Gmat_projection`: the vanishing of `det G_u` is `Diaz.det_Hmat` transported
along the real congruence of `Diaz.Hmat_real_congr` — `G_u = QᵀH_uQ`, so
`det G_u = (det Q)² det H_u = 0`.  That is where the hypothesis `u ū = r²`
enters; the trace and the idempotence of `G_u/(2r)` are direct computations in
the entries.
-/
import Mathlib
import Definitions.Def_Diaz_Rigidity
import Theorems.Thm_Diaz_det_Hmat
import Theorems.Thm_Diaz_Hmat_real_congr

open ComplexConjugate
open Diaz

open Diaz in
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
  · -- `G = QᵀHQ` and `det H = 0`
    rw [← Diaz.Hmat_real_congr u r x y hu, Matrix.det_mul, Matrix.det_mul,
      Diaz.det_Hmat h]
    ring
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
