-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.unit_pair_first_extension_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:24:11.973993+00:00
-- url     : https://prove2.me/submissions/bf4734f0-ef53-4acb-a84c-eefb271faab1

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Theorems.Thm_D1Bound5_IsD1Tuple_unit_pair_cubic_iteration
import Theorems.Thm_D1Bound5_complex_terminal_root_height
import Theorems.Thm_D1Bound5_full_ring_bennett_two_integer_k
import Theorems.Thm_D1Bound5_unit_pair_height_cutoff_from_orders

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual first extension of {-1,1} in an ordered six-tuple has
modulus below 10^4. The small branch, including modulus 8, is immediate;
the large branch derives both cubic growth and all Bennett inequalities
from the same actual tuple. No analytic certificate is a hypothesis. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hminus : a 0 = -1) (hplus : a 1 = 1)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖)) :
    ‖phi (a 2 : K)‖ < 10000 := by
  by_cases hS : 9 ≤ ‖phi (a 2 : K)‖
  swap
  · linarith only [lt_of_not_ge hS]
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  change 9 ≤ ‖f (a 2)‖ at hS
  have hm : f (a 0) = -1 := by rw [hminus,map_neg,map_one]
  have hp : f (a 1) = 1 := by rw [hplus,map_one]
  have hS0 : 0 < ‖f (a 2)‖ := by linarith only [hS]
  have hSD : ‖f (a 2)‖ ≤ ‖f (a 5)‖ := hmon (by decide : (2 : Fin 6) ≤ 5)
  have hD0 : 0 < ‖f (a 5)‖ := hS0.trans_le hSD
  have hgrowth : ‖f (a 2)‖^27/8192 < ‖f (a 5)‖ :=
    ha.unit_pair_cubic_iteration hK phi a hminus hplus hmon hS
  obtain ⟨rA,hrA⟩ := ha.2.2 0 2 (by decide)
  obtain ⟨rB,hrB⟩ := ha.2.2 1 2 (by decide)
  obtain ⟨vA,hvA⟩ := ha.2.2 0 5 (by decide)
  obtain ⟨vB,hvB⟩ := ha.2.2 1 5 (by decide)
  obtain ⟨z,hz⟩ := ha.2.2 2 5 (by decide)
  have hzC : (f z)^2 = f (a 2)*f (a 5)+1 := by
    simpa only [pow_two,map_mul,map_add,map_one] using congrArg f hz
  obtain ⟨hZ,hprod⟩ := complex_terminal_root_height (f (a 2)) (f (a 5)) (f z)
    (by linarith only [hS]) hSD hzC
  apply unit_pair_height_cutoff_from_orders ‖f (a 2)‖ ‖f (a 5)‖ ‖f z‖
    hS0 hD0 hZ hprod hgrowth
  intro hSbig k hk
  have hAB : ‖f (a 0)‖ ≤ ‖f (a 1)‖ := by rw [hm,hp]; norm_num
  have hAC : 1000 ≤ ‖f (a 0)‖*‖f (a 2)‖ := by
    rw [hm]
    norm_num only [norm_neg,norm_one,one_mul]
    linarith only [hSbig]
  have hC : 4*‖f (a 1)‖ < ‖f (a 2)‖ := by
    rw [hp]
    norm_num only [norm_one,mul_one]
    linarith only [hSbig]
  have hi := full_ring_bennett_two_integer_k hK phi (a 0) (a 1) (a 2) (a 5)
    rA rB vA vB z (ha.2.1 0) (ha.2.1 1) (ha.2.1 2) (ha.2.1 5)
    (ha.1.ne (by decide : (0 : Fin 6) ≠ 1))
    (by simpa only [pow_two] using hrA) (by simpa only [pow_two] using hrB)
    (by simpa only [pow_two] using hvA) (by simpa only [pow_two] using hvB)
    (by simpa only [pow_two] using hz) hAB hAC hC k hk
  change 1 < 3*‖f (a 2)‖*(42*‖f (a 1)‖^3*‖f (a 2)‖)^k/
    (‖f (a 1)‖*‖f z‖)+‖f z‖/(2*(bennettTwoResidualRate
      ‖f (a 0)‖ ‖f (a 1)‖ ‖f (a 2)‖ ‖f (a 0)-f (a 1)‖)^k) at hi
  rw [hm,hp] at hi
  norm_num [bennettTwoResidualRate] at hi
  exact hi

end D1Bound5
end
