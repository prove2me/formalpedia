-- Prove2me | solution 1 for D1Bound5.finiteA3_root_coefficient_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:12.729153+00:00
-- url     : https://prove2.me/submissions/e207f5cb-ca54-4594-97e0-aaeefee7d136

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
import Definitions.Def_D1Bound5_FiniteA3Coefficients_Definitions
import Definitions.Def_D1Bound5_FiniteHomogeneousTwo_Definitions
import Theorems.Thm_D1Bound5_finiteHomogeneousTwo_norm_le

section
namespace D1Bound5















theorem finiteA3_coefficient_sums_0 (i : Fin 3) :
    (∑ r, |(finiteA3Coeff0 i 0 r : ℝ)|)+
      (∑ r, |(finiteA3Coeff0 i 1 r : ℝ)|) = finiteA3CoefficientSums i 0 := by
  fin_cases i <;> norm_num [finiteA3Coeff0,finiteA3CoefficientSums,Fin.sum_univ_succ]

theorem finiteA3_coefficient_sums_1 (i : Fin 3) :
    (∑ r, |(finiteA3Coeff1 i 0 r : ℝ)|)+
      (∑ r, |(finiteA3Coeff1 i 1 r : ℝ)|) = finiteA3CoefficientSums i 1 := by
  fin_cases i <;> norm_num [finiteA3Coeff1,finiteA3CoefficientSums,Fin.sum_univ_succ]

theorem finiteA3_coefficient_sums_2 (i : Fin 3) :
    (∑ r, |(finiteA3Coeff2 i 0 r : ℝ)|)+
      (∑ r, |(finiteA3Coeff2 i 1 r : ℝ)|) = finiteA3CoefficientSums i 2 := by
  fin_cases i <;> norm_num [finiteA3Coeff2,finiteA3CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

theorem finiteA3_coefficient_sums_3 (i : Fin 3) :
    (∑ r, |(finiteA3Coeff3 i 0 r : ℝ)|)+
      (∑ r, |(finiteA3Coeff3 i 1 r : ℝ)|) = finiteA3CoefficientSums i 3 := by
  fin_cases i <;> norm_num [finiteA3Coeff3,finiteA3CoefficientSums,Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

end D1Bound5
end

section
namespace D1Bound5

/-- Each exact homogeneous coefficient pair has its own checked height. -/
theorem _root_.solution (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖)
    (i : Fin 3) (ell : Fin 4) :
    ‖finiteA3RootCoeff x y i 0 ell‖+‖finiteA3RootCoeff x y i 1 ell‖ ≤
      (finiteA3CoefficientSums i ell : ℝ)*‖y‖^(3+(ell : ℕ)) := by
  fin_cases ell
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 3 (finiteA3Coeff0 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 3 (finiteA3Coeff0 i 1) x y hxy)
    rw [← add_mul,finiteA3_coefficient_sums_0] at hh
    simpa [finiteA3RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 4 (finiteA3Coeff1 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 4 (finiteA3Coeff1 i 1) x y hxy)
    rw [← add_mul,finiteA3_coefficient_sums_1] at hh
    simpa [finiteA3RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 5 (finiteA3Coeff2 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 5 (finiteA3Coeff2 i 1) x y hxy)
    rw [← add_mul,finiteA3_coefficient_sums_2] at hh
    simpa [finiteA3RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using hh
  · have hh := add_le_add
      (finiteHomogeneousTwo_norm_le 6 (finiteA3Coeff3 i 0) x y hxy)
      (finiteHomogeneousTwo_norm_le 6 (finiteA3Coeff3 i 1) x y hxy)
    rw [← add_mul,finiteA3_coefficient_sums_3] at hh
    simpa [finiteA3RootCoeff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using hh









end D1Bound5
end
