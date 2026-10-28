-- Prove2me | solution 1 for D1Bound5.finiteA4_height_scaled
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:10.560223+00:00
-- url     : https://prove2.me/submissions/a3a77f56-0eac-402d-b463-58e5081eb20d

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
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteA4_root_columns_norm_le
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar

section
namespace D1Bound5



theorem finiteA4_coefficient_sums_nonneg (i : Fin 3) (ell : Fin 5) :
    0 ≤ (finiteA4CoefficientSums i ell : ℝ) := by
  fin_cases i <;> fin_cases ell <;> norm_num [finiteA4CoefficientSums, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

/-- Exact rational row checks preserve the manuscript's sharp M=165763. -/
theorem finiteA4_height_slack (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 5,
      (finiteA4CoefficientSums i ell : ℝ)/(1000 : ℝ)^(4-(ell : ℕ))) < 165763 := by
  fin_cases i <;> norm_num [finiteA4CoefficientSums,Fin.sum_univ_succ]



/-- Actual integral A4 root-column height. No coefficient table or bound
is an input hypothesis: all coefficients and the strict margin are proved. -/
theorem _root_.solution (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖) <
      165763*‖y‖^9*‖c‖^4 := by
  have hnorm := mul_le_mul_of_nonneg_left (finiteA4_root_columns_norm_le x y c hxy i)
    (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 4
    (fun ell => (finiteA4CoefficientSums i ell : ℝ)) (finiteA4_coefficient_sums_nonneg i)
    165763 (‖y‖*‖c‖) hYC (finiteA4_height_slack i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 5)
  have heq : (101/100 : ℝ)*(‖y‖^5*∑ ell : Fin 5,
      (finiteA4CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ)) <
      165763*‖y‖^9*‖c‖^4 := by
    calc
      (101/100 : ℝ)*(‖y‖^5*∑ ell : Fin 5,
          (finiteA4CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ)) =
          ‖y‖^5*((101/100 : ℝ)*(∑ ell : Fin 5,
            (finiteA4CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ))) := by ring
      _ < ‖y‖^5*(165763*(‖y‖*‖c‖)^4) := hm
      _ = 165763*‖y‖^9*‖c‖^4 := by ring
  exact hnorm.trans_lt heq

end D1Bound5
end
