-- Prove2me | solution 1 for D1Bound5.finiteA5_root_coefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:21:27.554135+00:00
-- url     : https://prove2.me/submissions/e5bee4ba-ff02-4d08-939e-0ffaa9726b6d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA5Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le

section
namespace D1Bound5


































theorem finiteA5_coefficient_sums_0 (i : Fin 3) :
    (∑ r, |(finiteA5Coeff0 i 0 r : ℝ)|)+
      (∑ r, |(finiteA5Coeff0 i 1 r : ℝ)|) = finiteA5CoefficientSums i 0 := by
  fin_cases i <;> norm_num [finiteA5Coeff0,finiteA5CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]

theorem finiteA5_coefficient_sums_1 (i : Fin 3) :
    (∑ r, |(finiteA5Coeff1 i 0 r : ℝ)|)+
      (∑ r, |(finiteA5Coeff1 i 1 r : ℝ)|) = finiteA5CoefficientSums i 1 := by
  fin_cases i <;> norm_num [finiteA5Coeff1,finiteA5CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]

theorem finiteA5_coefficient_sums_2 (i : Fin 3) :
    (∑ r, |(finiteA5Coeff2 i 0 r : ℝ)|)+
      (∑ r, |(finiteA5Coeff2 i 1 r : ℝ)|) = finiteA5CoefficientSums i 2 := by
  fin_cases i <;> norm_num [finiteA5Coeff2,finiteA5CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]

theorem finiteA5_coefficient_sums_3 (i : Fin 3) :
    (∑ r, |(finiteA5Coeff3 i 0 r : ℝ)|)+
      (∑ r, |(finiteA5Coeff3 i 1 r : ℝ)|) = finiteA5CoefficientSums i 3 := by
  fin_cases i <;> norm_num [finiteA5Coeff3,finiteA5CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]

theorem finiteA5_coefficient_sums_4 (i : Fin 3) :
    (∑ r, |(finiteA5Coeff4 i 0 r : ℝ)|)+
      (∑ r, |(finiteA5Coeff4 i 1 r : ℝ)|) = finiteA5CoefficientSums i 4 := by
  fin_cases i <;> norm_num [finiteA5Coeff4,finiteA5CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]

theorem finiteA5_coefficient_sums_5 (i : Fin 3) :
    (∑ r, |(finiteA5Coeff5 i 0 r : ℝ)|)+
      (∑ r, |(finiteA5Coeff5 i 1 r : ℝ)|) = finiteA5CoefficientSums i 5 := by
  fin_cases i <;> norm_num [finiteA5Coeff5,finiteA5CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] <;> rfl

end D1Bound5
end

section
namespace D1Bound5

/-- Each exact homogeneous coefficient pair has its own checked height. -/
theorem _root_.solution (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖)
    (i : Fin 3) (ell : Fin 6) :
    ‖finiteA5RootCoeff x y i 0 ell‖+‖finiteA5RootCoeff x y i 1 ell‖ ≤
      (finiteA5CoefficientSums i ell : ℝ)*‖y‖^(7+(ell : ℕ)) := by
  fin_cases ell
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 7 (finiteA5Coeff0 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 7 (finiteA5Coeff0 i 1) x y hxy)
    rw [← add_mul,finiteA5_coefficient_sums_0] at hh
    simpa [finiteA5RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 8 (finiteA5Coeff1 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 8 (finiteA5Coeff1 i 1) x y hxy)
    rw [← add_mul,finiteA5_coefficient_sums_1] at hh
    simpa [finiteA5RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 9 (finiteA5Coeff2 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 9 (finiteA5Coeff2 i 1) x y hxy)
    rw [← add_mul,finiteA5_coefficient_sums_2] at hh
    simpa [finiteA5RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 10 (finiteA5Coeff3 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 10 (finiteA5Coeff3 i 1) x y hxy)
    rw [← add_mul,finiteA5_coefficient_sums_3] at hh
    simpa [finiteA5RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 11 (finiteA5Coeff4 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 11 (finiteA5Coeff4 i 1) x y hxy)
    rw [← add_mul,finiteA5_coefficient_sums_4] at hh
    simpa [finiteA5RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 12 (finiteA5Coeff5 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 12 (finiteA5Coeff5 i 1) x y hxy)
    rw [← add_mul,finiteA5_coefficient_sums_5] at hh
    simpa [finiteA5RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons] using hh









end D1Bound5
end
