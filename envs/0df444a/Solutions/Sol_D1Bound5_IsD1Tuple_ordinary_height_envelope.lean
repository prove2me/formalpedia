-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.ordinary_height_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:43:04.833269+00:00
-- url     : https://prove2.me/submissions/cd99baf3-63f6-4aa5-8a52-15f3650ad58e

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
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_bennettTwoResidualRate_pos
import Theorems.Thm_D1Bound5_complex_terminal_root_height
import Theorems.Thm_D1Bound5_full_ring_bennett_two_integer_k
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_ordinary_height_envelope_from_orders

section
open scoped NumberField
open Module

namespace D1Bound5



/-- The manuscript ordinary height envelope for an actual ordered
D(1)-quadruple. The all-order analytic estimate is obtained internally
from the constructed integral Bennett matrix and the tuple's roots. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hAC : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (a 2 : K)‖)
    (hC : 4*‖phi (a 1 : K)‖ < ‖phi (a 2 : K)‖)
    (h r u : ℝ)
    (hHlog : ordinaryLog10 (42*‖phi (a 1 : K)‖^3*‖phi (a 2 : K)‖) <
      ordinaryLog10 ‖phi (a 2 : K)‖+h)
    (hRlog : 2*ordinaryLog10 ‖phi (a 2 : K)‖+r <
      ordinaryLog10 (bennettTwoResidualRate ‖phi (a 0 : K)‖ ‖phi (a 1 : K)‖
        ‖phi (a 2 : K)‖ ‖phi (a 0 : K)-phi (a 1 : K)‖))
    (hUlog : ordinaryLog10 (253*‖phi (a 1 : K)‖^2) < u)
    (hxt : h-r < ordinaryLog10 ‖phi (a 2 : K)‖)
    (hx2 : 0 < 2*ordinaryLog10 ‖phi (a 2 : K)‖+r) :
    ordinaryLog10 ‖phi (a 3 : K)‖ < 7*ordinaryLog10 ‖phi (a 2 : K)‖+
      (4*u+8*h-4*r)+(2*u*r+(4*u+8*h-4*r)*(h-r))/
        (ordinaryLog10 ‖phi (a 2 : K)‖-(h-r))+(2/5 : ℝ) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  change 4 * ‖f (a 1)‖ < ‖f (a 2)‖ at hC
  change 1000 ≤ ‖f (a 0)‖ * ‖f (a 2)‖ at hAC
  have hA1 : 1 ≤ ‖f (a 0)‖ := one_le_norm_integer hK phi (ha.2.1 0)
  have hB1 : 1 ≤ ‖f (a 1)‖ := one_le_norm_integer hK phi (ha.2.1 1)
  have hD1 : 1 ≤ ‖f (a 3)‖ := one_le_norm_integer hK phi (ha.2.1 3)
  have hA0 : 0 < ‖f (a 0)‖ := by linarith only [hA1]
  have hB0 : 0 < ‖f (a 1)‖ := by linarith only [hB1]
  have hD0 : 0 < ‖f (a 3)‖ := by linarith only [hD1]
  have hC2 : 2 ≤ ‖f (a 2)‖ := by linarith only [hC,hB1]
  have hC1 : 1 < ‖f (a 2)‖ := by linarith only [hC2]
  have hdelta1 : 1 ≤ ‖f (a 0)-f (a 1)‖ := by
    have hh := one_le_norm_integer hK phi
      (sub_ne_zero.mpr (ha.1.ne (by decide : (0 : Fin 4) ≠ 1)))
    change 1 ≤ ‖f (a 0-a 1)‖ at hh
    simpa only [map_sub] using hh
  have hdelta : 0 < ‖f (a 0)-f (a 1)‖ := by linarith only [hdelta1]
  have hrate := bennettTwoResidualRate_pos ‖f (a 0)‖ ‖f (a 1)‖ ‖f (a 2)‖
    ‖f (a 0)-f (a 1)‖ hA0 hB0 hdelta (by linarith only [hAC])
  obtain ⟨rA,hrA⟩ := ha.2.2 0 2 (by decide)
  obtain ⟨rB,hrB⟩ := ha.2.2 1 2 (by decide)
  obtain ⟨vA,hvA⟩ := ha.2.2 0 3 (by decide)
  obtain ⟨vB,hvB⟩ := ha.2.2 1 3 (by decide)
  obtain ⟨z,hz⟩ := ha.2.2 2 3 (by decide)
  have hzC : (f z)^2 = f (a 2)*f (a 3)+1 := by
    simpa only [pow_two,map_mul,map_add,map_one] using congrArg f hz
  obtain ⟨hZ,hprod⟩ := complex_terminal_root_height (f (a 2)) (f (a 3)) (f z)
    hC2 (hmon (by decide : (2 : Fin 4) ≤ 3)) hzC
  apply ordinary_height_envelope_from_orders ‖f (a 1)‖ ‖f (a 2)‖ ‖f (a 3)‖ ‖f z‖
    (bennettTwoResidualRate ‖f (a 0)‖ ‖f (a 1)‖ ‖f (a 2)‖ ‖f (a 0)-f (a 1)‖)
    h r u hB1 hC1 hD0 hZ hrate hprod hHlog hRlog hUlog hxt hx2
  intro k hk
  exact full_ring_bennett_two_integer_k hK phi (a 0) (a 1) (a 2) (a 3)
    rA rB vA vB z (ha.2.1 0) (ha.2.1 1) (ha.2.1 2) (ha.2.1 3)
    (ha.1.ne (by decide : (0 : Fin 4) ≠ 1))
    (by simpa only [pow_two] using hrA) (by simpa only [pow_two] using hrB)
    (by simpa only [pow_two] using hvA) (by simpa only [pow_two] using hvB)
    (by simpa only [pow_two] using hz) (hmon (by decide : (0 : Fin 4) ≤ 1))
    hAC hC k hk

end D1Bound5
end
