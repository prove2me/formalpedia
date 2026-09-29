-- Prove2me | solution 1 for Diaz.Hmat_pencil_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:42.367235+00:00
-- url     : https://prove2.me/submissions/a04400b4-a95b-4795-8ff9-5d48853edb9e

import Mathlib
import Definitions.Def_Diaz_Rigidity

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {u r : ℂ} (hr : r ≠ 0) :
    !![0, r; r, 0] *
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) + u • !![0, 0; r⁻¹, 0] + (conj u) • !![0, r⁻¹; 0, 0])
        = Hmat u r
      ∧ (!![0, 0; r⁻¹, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 0; r⁻¹, 0] = 0
      ∧ (!![0, r⁻¹; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, r⁻¹; 0, 0] = 0
      ∧ Matrix.trace ((!![0, 0; r⁻¹, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, r⁻¹; 0, 0])
          = (r ^ 2)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Hmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> field_simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [Matrix.trace_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
