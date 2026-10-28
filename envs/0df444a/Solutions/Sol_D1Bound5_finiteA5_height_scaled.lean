-- Prove2me | solution 1 for D1Bound5.finiteA5_height_scaled
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:40.674038+00:00
-- url     : https://prove2.me/submissions/1703e1cc-23f5-40cc-be9f-6a27fbcb6c5d

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
import Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteA5_root_columns_norm_le
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar

section
namespace D1Bound5



theorem finiteA5_coefficient_sums_nonneg (i : Fin 3) (ell : Fin 6) :
    0 ≤ (finiteA5CoefficientSums i ell : ℝ) := by
  fin_cases i <;> fin_cases ell <;> norm_num [finiteA5CoefficientSums, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]

/-- Exact rational row checks preserve the manuscript's sharp M=3113013. -/
theorem finiteA5_height_slack (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 6,
      (finiteA5CoefficientSums i ell : ℝ)/(1000 : ℝ)^(5-(ell : ℕ))) < 3113013 := by
  fin_cases i <;> norm_num [finiteA5CoefficientSums,Fin.sum_univ_succ]



/-- Actual integral A5 root-column height. No coefficient table or bound
is an input hypothesis: all coefficients and the strict margin are proved. -/
theorem _root_.solution (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA5Left x y c i‖+‖finiteA5Right x y c i‖) <
      3113013*‖y‖^12*‖c‖^5 := by
  have hnorm := mul_le_mul_of_nonneg_left (finiteA5_root_columns_norm_le x y c hxy i)
    (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 5
    (fun ell => (finiteA5CoefficientSums i ell : ℝ)) (finiteA5_coefficient_sums_nonneg i)
    3113013 (‖y‖*‖c‖) hYC (finiteA5_height_slack i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 7)
  have heq : (101/100 : ℝ)*(‖y‖^7*∑ ell : Fin 6,
      (finiteA5CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ)) <
      3113013*‖y‖^12*‖c‖^5 := by
    calc
      (101/100 : ℝ)*(‖y‖^7*∑ ell : Fin 6,
          (finiteA5CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ)) =
          ‖y‖^7*((101/100 : ℝ)*(∑ ell : Fin 6,
            (finiteA5CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ))) := by ring
      _ < ‖y‖^7*(3113013*(‖y‖*‖c‖)^5) := hm
      _ = 3113013*‖y‖^12*‖c‖^5 := by ring
  exact hnorm.trans_lt heq

end D1Bound5
end
