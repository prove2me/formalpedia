-- Prove2me | solution 1 for D1Bound5.finiteA4_root_columns_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:52.100705+00:00
-- url     : https://prove2.me/submissions/7f925df9-17bd-4e64-b7ad-ed5fd44c0cd4

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
import Theorems.Thm_D1Bound5_finiteA4_root_coeff_decomposition
import Theorems.Thm_D1Bound5_finiteA4_root_coefficient_norm_le
import Theorems.Thm_D1Bound5_finitePolynomial_two_columns_norm_le

section
namespace D1Bound5







theorem _root_.solution (x y c : ℂ) (hxy : ‖x‖ ≤ ‖y‖) (i : Fin 3) :
    ‖finiteA4Left x y c i‖+‖finiteA4Right x y c i‖ ≤
      ‖y‖^5*∑ ell : Fin 5, (finiteA4CoefficientSums i ell : ℝ)*(‖y‖*‖c‖)^(ell : ℕ) := by
  have h0 := finiteA4_root_coeff_decomposition x y c i 0
  have h1 := finiteA4_root_coeff_decomposition x y c i 1
  change finiteA4Left x y c i = _ at h0
  change finiteA4Right x y c i = _ at h1
  rw [h0,h1]
  exact finitePolynomial_two_columns_norm_le 4 5 (finiteA4RootCoeff x y i)
    (fun ell => (finiteA4CoefficientSums i ell : ℝ)) c ‖y‖
    (finiteA4_root_coefficient_norm_le x y hxy i)



end D1Bound5
end
