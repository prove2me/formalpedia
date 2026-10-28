-- Prove2me | solution 1 for D1Bound5.finiteA5_root_columns_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:49.580028+00:00
-- url     : https://prove2.me/submissions/39737e1c-4dbc-4cf4-a1ce-f24628d7fded

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
import Theorems.Thm_D1Bound5_finiteA5_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finiteA5_root_coefficient_norm_le
import Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le

section
namespace D1Bound5







theorem _root_.solution (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteA5Left x y c i‖+‖finiteA5Right x y c i‖ ≤
      ‖y‖^7*∑ ell : Fin 6, (finiteA5CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ) := by
  have h0 := finiteA5_root_coeff_decomposition x y c i 0
  have h1 := finiteA5_root_coeff_decomposition x y c i 1
  change finiteA5Left x y c i = _ at h0
  change finiteA5Right x y c i = _ at h1
  rw [h0,h1]
  exact finitePolynomial_two_columns_norm_le 5 7 (finiteA5RootCoeff x y i)
    (fun ell => (finiteA5CoefficientSums i ell : ℝ)) c ‖y‖
    (finiteA5_root_coefficient_norm_le x y hxy i)



end D1Bound5
end
