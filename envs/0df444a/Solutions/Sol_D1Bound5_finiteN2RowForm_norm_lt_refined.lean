-- Prove2me | solution 1 for D1Bound5.finiteN2RowForm_norm_lt_refined
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:53.841906+00:00
-- url     : https://prove2.me/submissions/35df7b37-6180-4c63-9989-625f549dbb44

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteN2IntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteN2Matrix_Definitions
import Definitions.Def_D1Bound5_FiniteN2Residual_Definitions
import Theorems.Thm_D1Bound5_finiteN2RowForm_eq_root_sum
import Theorems.Thm_D1Bound5_finite_row_root_transfer_norm_lt

section
open scoped NumberField
open Module

namespace D1Bound5

/-- An explicit coefficient-height refinement for the actual finite N2 row.
The full-ring application supplies the actual residual bound separately. -/
theorem _root_.solution
    (x y c z sX sY : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (i : Fin 3) (M : ℝ)
    (hheightScaled : (101/100 : ℝ)*(‖finiteN2Left x y c i‖+‖finiteN2Right x y c i‖) <
      M*‖y‖^4*‖c‖^2)
    (herr : ∀ j : Fin 2,
      ‖(1+1/(![x,y] j*c))^(1/2 : ℂ)-![sX,sY] j/(![x,y] j*z)‖ ≤
        (101/100 : ℝ)*‖c‖/(‖![x,y] j‖*‖z‖^2))
    (R : ℝ) (hres : ‖finiteN2Residual x y c i‖ < R) :
    ‖finiteN2RowForm x y c z sX sY i‖ <
      M*‖y‖^4*‖c‖^3/‖z‖+R*‖z‖ := by
  have ha (j : Fin 2) : ![x,y] j ≠ 0 := by fin_cases j <;> assumption
  have hh := hheightScaled
  have hheight : (∑ j : Fin 2, ‖![finiteN2Left x y c i,finiteN2Right x y c i] j‖) ≤
      (M*‖y‖^4*‖c‖^2)/(101/100 : ℝ) := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 101/100)).mpr
    nlinarith only [hh.le]
  have hres' : ‖finiteN2Constant x y c i +
      ∑ j : Fin 2, ![x,y] j * ![finiteN2Left x y c i,finiteN2Right x y c i] j *
        (1+1/(![x,y] j*c))^(1/2 : ℂ)‖ < R := by
    simpa [Fin.sum_univ_two, finiteN2Residual, add_assoc] using hres
  have h := finite_row_root_transfer_norm_lt (finiteN2Constant x y c i) z
    ![x,y] ![finiteN2Left x y c i,finiteN2Right x y c i]
    (fun j => (1+1/(![x,y] j*c))^(1/2 : ℂ)) ![sX,sY]
    ha hz ((101/100 : ℝ)*‖c‖) ((M*‖y‖^4*‖c‖^2)/(101/100 : ℝ)) R
    (by positivity) herr hheight hres'
  rw [finiteN2RowForm_eq_root_sum]
  convert h using 1 <;> ring



end D1Bound5
end
