-- Prove2me | solution 1 for D1Bound5.finiteMRowForm_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:53:28.09291+00:00
-- url     : https://prove2.me/submissions/bd31e4e4-1eae-42fd-b8c2-22eb00301bc0

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
import Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteMMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteMResidualPoint_Definitions
import Definitions.Def_D1Bound5_FiniteMRowBound_Definitions
import Theorems.Thm_D1Bound5_finiteMDividedMatrix_root_height
import Theorems.Thm_D1Bound5_finiteMResidual_eq_root_sum
import Theorems.Thm_D1Bound5_finiteM_residual_norm_lt
import Theorems.Thm_D1Bound5_finite_row_root_transfer_norm_lt

section
namespace D1Bound5





theorem finiteMRowForm_eq_root_sum (a b s c z rA rB rS : ℂ) (i : Fin 4) :
    finiteMRowForm a b s c z rA rB rS i =
      finiteMDividedMatrix a b s c i 0*z+
        ∑ j : Fin 3, finiteMDividedMatrix a b s c i j.succ*![rA,rB,rS] j := by
  simp [finiteMRowForm,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc]

/-- Transfer the actual ordinary-three order-two residual to the
original integral row, using its proved finite coefficient height. -/
theorem _root_.solution
    (a b s c z rA rB rS : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s)
    (hA : 1 ≤ ‖a‖) (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖)
    (hC : 1 ≤ ‖c‖) (hAC : 1000 ≤ ‖a‖*‖c‖)
    (herr : ∀ j : Fin 3,
      ‖(1+1/(finiteMAnchors a b s j*c))^(1/2 : ℂ)-
        ![rA,rB,rS] j/(finiteMAnchors a b s j*z)‖ ≤
          (3/2 : ℝ)*‖c‖/(‖finiteMAnchors a b s j‖*‖z‖^2)) (i : Fin 4) :
    ‖finiteMRowForm a b s c z rA rB rS i‖ <
      (8/9 : ℝ)*608^2*‖b‖^3*‖s‖^8*‖c‖^3/‖z‖+
        (3920/81 : ℝ)*‖b‖^2*‖s‖^5*‖z‖/(‖a‖^3*‖c‖^6) := by
  have hheight := finiteMDividedMatrix_root_height a b s c (hA.trans hAB) hAB hBS hC i
  have hres := finiteM_residual_norm_lt a b s c ha hb hs hc hab has hbs hA hAB hBS hAC i
  rw [finiteMResidual_eq_root_sum a b s c ha hb hs hc i] at hres
  have hanchors : ∀ j, finiteMAnchors a b s j ≠ 0 := by
    intro j
    fin_cases j
    · exact ha
    · exact hb
    · exact hs
  have hh := finite_row_root_transfer_norm_lt (finiteMDividedMatrix a b s c i 0) z
    (finiteMAnchors a b s) (fun j => finiteMDividedMatrix a b s c i j.succ)
    (fun j => (1+1/(finiteMAnchors a b s j*c))^(1/2 : ℂ)) ![rA,rB,rS]
    hanchors hz ((3/2 : ℝ)*‖c‖) (169728*‖b‖^3*‖s‖^8*‖c‖^2)
    ((3920/81 : ℝ)*‖b‖^2*‖s‖^5/(‖a‖^3*‖c‖^6)) (by positivity) herr hheight hres
  rw [finiteMRowForm_eq_root_sum]
  apply hh.trans
  have hp : 0 < ‖b‖^3*‖s‖^8*‖c‖^3/‖z‖ := by
    exact div_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr hb) 3)
      (pow_pos (norm_pos_iff.mpr hs) 8)) (pow_pos (norm_pos_iff.mpr hc) 3)) (norm_pos_iff.mpr hz)
  have hcoef : (254592 : ℝ)*(‖b‖^3*‖s‖^8*‖c‖^3/‖z‖) <
      ((8/9 : ℝ)*608^2)*(‖b‖^3*‖s‖^8*‖c‖^3/‖z‖) :=
    mul_lt_mul_of_pos_right (by norm_num) hp
  calc
    _ = 254592*(‖b‖^3*‖s‖^8*‖c‖^3/‖z‖) +
        (3920/81 : ℝ)*‖b‖^2*‖s‖^5*‖z‖/(‖a‖^3*‖c‖^6) := by ring
    _ < ((8/9 : ℝ)*608^2)*(‖b‖^3*‖s‖^8*‖c‖^3/‖z‖) +
        (3920/81 : ℝ)*‖b‖^2*‖s‖^5*‖z‖/(‖a‖^3*‖c‖^6) :=
      by linarith only [hcoef]
    _ = _ := by ring

end D1Bound5
end
