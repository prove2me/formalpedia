-- Prove2me | solution 1 for D1Bound5.phaseVandermondeRatio_le_ratio_triangle
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:15.325831+00:00
-- url     : https://prove2.me/submissions/3e918122-3f11-43f2-b0bb-b264c4780674

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5



theorem _root_.solution (a b s : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hB : 0 < ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) (hAB : ‖a‖ ≤ r*‖b‖) :
    phaseVandermondeRatio a b s ≤ 2*(1+r)^2 := by
  have hS : 0 < ‖s‖ := hB.trans_le hBS
  have h01 : ‖a-b‖ ≤ (1+r)*‖b‖ := by
    have hh := norm_sub_le a b
    nlinarith only [hh,hAB]
  have h02 : ‖a-s‖ ≤ (1+r)*‖s‖ := by
    have hh := norm_sub_le a s
    have hh' := mul_le_mul_of_nonneg_left hBS hr
    nlinarith only [hh,hAB,hh']
  have h12 : ‖b-s‖ ≤ 2*‖s‖ := by
    have hh := norm_sub_le b s
    linarith only [hh,hBS]
  have hprod : ‖(a-b)*(a-s)*(b-s)‖ ≤ 2*(1+r)^2*(‖b‖*‖s‖^2) := by
    calc
      _ = ‖a-b‖*‖a-s‖*‖b-s‖ := by rw [norm_mul,norm_mul]
      _ ≤ ((1+r)*‖b‖)*((1+r)*‖s‖)*(2*‖s‖) := by gcongr
      _ = _ := by ring
  exact (div_le_iff₀ (by positivity : 0 < ‖b‖*‖s‖^2)).mpr hprod



end D1Bound5
end
