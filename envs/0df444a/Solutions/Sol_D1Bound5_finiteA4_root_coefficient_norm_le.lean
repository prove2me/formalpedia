-- Prove2me | solution 1 for D1Bound5.finiteA4_root_coefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:52:00.549013+00:00
-- url     : https://prove2.me/submissions/f6c5e063-3091-4890-9f36-7e129a2c6856

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
import Definitions.Def_D1Bound5_FiniteA4Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le

section
namespace D1Bound5

















theorem finiteA4_coefficient_sums_0 (i : Fin 3) :
    (∑ r, |(finiteA4Coeff0 i 0 r : ℝ)|)+
      (∑ r, |(finiteA4Coeff0 i 1 r : ℝ)|) = finiteA4CoefficientSums i 0 := by
  fin_cases i <;> norm_num [finiteA4Coeff0,finiteA4CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem finiteA4_coefficient_sums_1 (i : Fin 3) :
    (∑ r, |(finiteA4Coeff1 i 0 r : ℝ)|)+
      (∑ r, |(finiteA4Coeff1 i 1 r : ℝ)|) = finiteA4CoefficientSums i 1 := by
  fin_cases i <;> norm_num [finiteA4Coeff1,finiteA4CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem finiteA4_coefficient_sums_2 (i : Fin 3) :
    (∑ r, |(finiteA4Coeff2 i 0 r : ℝ)|)+
      (∑ r, |(finiteA4Coeff2 i 1 r : ℝ)|) = finiteA4CoefficientSums i 2 := by
  fin_cases i <;> norm_num [finiteA4Coeff2,finiteA4CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem finiteA4_coefficient_sums_3 (i : Fin 3) :
    (∑ r, |(finiteA4Coeff3 i 0 r : ℝ)|)+
      (∑ r, |(finiteA4Coeff3 i 1 r : ℝ)|) = finiteA4CoefficientSums i 3 := by
  fin_cases i <;> norm_num [finiteA4Coeff3,finiteA4CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

theorem finiteA4_coefficient_sums_4 (i : Fin 3) :
    (∑ r, |(finiteA4Coeff4 i 0 r : ℝ)|)+
      (∑ r, |(finiteA4Coeff4 i 1 r : ℝ)|) = finiteA4CoefficientSums i 4 := by
  fin_cases i <;> norm_num [finiteA4Coeff4,finiteA4CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

end D1Bound5
end

section
namespace D1Bound5

/-- Each exact homogeneous coefficient pair has its own checked height. -/
theorem _root_.solution (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖)
    (i : Fin 3) (ell : Fin 5) :
    ‖finiteA4RootCoeff x y i 0 ell‖+‖finiteA4RootCoeff x y i 1 ell‖ ≤
      (finiteA4CoefficientSums i ell : ℝ)*‖y‖^(5+(ell : ℕ)) := by
  fin_cases ell
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 5 (finiteA4Coeff0 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 5 (finiteA4Coeff0 i 1) x y hxy)
    rw [← add_mul,finiteA4_coefficient_sums_0] at hh
    simpa [finiteA4RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 6 (finiteA4Coeff1 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 6 (finiteA4Coeff1 i 1) x y hxy)
    rw [← add_mul,finiteA4_coefficient_sums_1] at hh
    simpa [finiteA4RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 7 (finiteA4Coeff2 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 7 (finiteA4Coeff2 i 1) x y hxy)
    rw [← add_mul,finiteA4_coefficient_sums_2] at hh
    simpa [finiteA4RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 8 (finiteA4Coeff3 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 8 (finiteA4Coeff3 i 1) x y hxy)
    rw [← add_mul,finiteA4_coefficient_sums_3] at hh
    simpa [finiteA4RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 9 (finiteA4Coeff4 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 9 (finiteA4Coeff4 i 1) x y hxy)
    rw [← add_mul,finiteA4_coefficient_sums_4] at hh
    simpa [finiteA4RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using hh









end D1Bound5
end
