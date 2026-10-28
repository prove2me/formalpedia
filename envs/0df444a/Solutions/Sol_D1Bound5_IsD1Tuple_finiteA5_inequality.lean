-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.finiteA5_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:35:23.090468+00:00
-- url     : https://prove2.me/submissions/b533e87d-6acb-4871-abfd-0becdcb0ab71

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
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_full_ring_finiteA5_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The A5 family on any actual four-entry subtuple. The matrix uses the unequal pole orders specified in the article. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hXY : ‖phi (t 0 : K)‖ ≤ ‖phi (t 1 : K)‖)
    (hXC : 1000 ≤ ‖phi (t 0 : K)‖*‖phi (t 2 : K)‖)
    (hC : 200*‖phi (t 1 : K)‖ ≤ ‖phi (t 2 : K)‖) :
    ∃ z : 𝓞 K, z^2=t 2*t 3+1 ∧
      1 < 3113013*‖phi (t 1 : K)‖^12*‖phi (t 2 : K)‖^6/‖phi (z : K)‖ +
        (495/64 : ℝ)*‖phi (t 1 : K)‖^5*‖phi (z : K)‖/
          (‖phi (t 0 : K)‖^6*‖phi (t 2 : K)‖^9) := by
  obtain ⟨rX,hrX⟩ := ht.2.2 0 2 (by decide)
  obtain ⟨rY,hrY⟩ := ht.2.2 1 2 (by decide)
  obtain ⟨vX,hvX⟩ := ht.2.2 0 3 (by decide)
  obtain ⟨vY,hvY⟩ := ht.2.2 1 3 (by decide)
  obtain ⟨z,hz⟩ := ht.2.2 2 3 (by decide)
  have hz' : z^2=t 2*t 3+1 := by simpa only [pow_two] using hz
  refine ⟨z,hz',?_⟩
  exact full_ring_finiteA5_integer hK phi (t 0) (t 1) (t 2) (t 3) rX rY vX vY z
    (ht.2.1 0) (ht.2.1 1) (ht.2.1 2) (ht.2.1 3)
    (fun h => (by decide : (0 : Fin 4) ≠ 1) (ht.1 h))
    (by simpa only [pow_two] using hrX) (by simpa only [pow_two] using hrY)
    (by simpa only [pow_two] using hvX) (by simpa only [pow_two] using hvY)
    hz' hXY hXC hC



end D1Bound5
end
