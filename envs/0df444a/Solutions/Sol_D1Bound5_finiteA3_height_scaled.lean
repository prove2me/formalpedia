-- Prove2me | solution 1 for D1Bound5.finiteA3_height_scaled
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:45:38.416465+00:00
-- url     : https://prove2.me/submissions/c54e0753-dc11-4576-90d0-5b1059f24334

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
import Definitions.Def_D1Bound5_FiniteA3Matrix_Definitions
import Theorems.Thm_D1Bound5_finiteA3_root_columns_norm_le
import Theorems.Thm_D1Bound5_finitePolynomial_height_scalar

section
namespace D1Bound5



theorem finiteA3_coefficient_sums_nonneg (i : Fin 3) (ell : Fin 4) :
    0 ≤ (finiteA3CoefficientSums i ell : ℝ) := by
  fin_cases i <;> fin_cases ell <;> norm_num [finiteA3CoefficientSums, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- Exact rational row checks preserve the manuscript's sharp M=2265. -/
theorem finiteA3_height_slack (i : Fin 3) :
    (101/100 : ℝ)*(∑ ell : Fin 4,
      (finiteA3CoefficientSums i ell : ℝ)/(1000 : ℝ)^(3-(ell : ℕ))) < 2265 := by
  fin_cases i <;> norm_num [finiteA3CoefficientSums,Fin.sum_univ_succ]



/-- Actual integral A3 root-column height. No coefficient table or bound
is an input hypothesis: all coefficients and the strict margin are proved. -/
theorem _root_.solution (x y c : ℂ) (hy : y ≠ 0)
    (hxy : ‖x‖ ≤ ‖y‖) (hYC : 1000 ≤ ‖y‖*‖c‖) (i : Fin 3) :
    (101/100 : ℝ)*(‖finiteA3Left x y c i‖+‖finiteA3Right x y c i‖) <
      2265*‖y‖^6*‖c‖^3 := by
  have hnorm := mul_le_mul_of_nonneg_left (finiteA3_root_columns_norm_le x y c hxy i)
    (show (0 : ℝ) ≤ 101/100 by norm_num)
  have hs := finitePolynomial_height_scalar 3
    (fun ell => (finiteA3CoefficientSums i ell : ℝ)) (finiteA3_coefficient_sums_nonneg i)
    2265 (‖y‖*‖c‖) hYC (finiteA3_height_slack i)
  have hm := mul_lt_mul_of_pos_left hs (pow_pos (norm_pos_iff.mpr hy) 3)
  have heq : (101/100 : ℝ)*(‖y‖^3*∑ ell : Fin 4,
      (finiteA3CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ)) <
      2265*‖y‖^6*‖c‖^3 := by
    calc
      (101/100 : ℝ)*(‖y‖^3*∑ ell : Fin 4,
          (finiteA3CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ)) =
          ‖y‖^3*((101/100 : ℝ)*(∑ ell : Fin 4,
            (finiteA3CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ))) := by ring
      _ < ‖y‖^3*(2265*(‖y‖*‖c‖)^3) := hm
      _ = 2265*‖y‖^6*‖c‖^3 := by ring
  exact hnorm.trans_lt heq

end D1Bound5
end
