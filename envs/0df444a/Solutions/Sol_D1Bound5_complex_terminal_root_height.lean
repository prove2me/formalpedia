-- Prove2me | solution 1 for D1Bound5.complex_terminal_root_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:47.353307+00:00
-- url     : https://prove2.me/submissions/266a7602-9a54-47c7-ae6f-f681502c8d22

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
open scoped NumberField
open Module

namespace D1Bound5

/-- A terminal square root supplies the height comparison and is
automatically nonzero in the ordered large-entry regime. -/
theorem _root_.solution (c d z : ℂ)
    (hC : 2 ≤ ‖c‖) (hCD : ‖c‖ ≤ ‖d‖) (hz : z^2 = c*d+1) :
    1 ≤ ‖z‖ ∧ ‖c‖*‖d‖ < 2*‖z‖^2 := by
  have hD : 2 ≤ ‖d‖ := hC.trans hCD
  have hCD4 : 4 ≤ ‖c‖*‖d‖ := by
    have hp := mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)
    nlinarith only [hp,hC,hD]
  have hZ : ‖c‖*‖d‖ ≤ ‖z‖^2+1 := by
    have hid : c*d = z^2-1 := by rw [hz]; ring
    have hh := norm_sub_le (z^2) (1 : ℂ)
    rw [← hid,norm_mul] at hh
    simpa only [norm_pow,norm_one] using hh
  constructor
  · by_contra hbad
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hbad)))
      (show 0 ≤ 1+‖z‖ by positivity)
    nlinarith only [hZ,hCD4,hp]
  · nlinarith only [hZ,hCD4]



end D1Bound5
end
