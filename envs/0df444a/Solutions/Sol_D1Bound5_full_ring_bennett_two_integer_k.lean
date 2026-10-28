-- Prove2me | solution 1 for D1Bound5.full_ring_bennett_two_integer_k
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:23:19.620444+00:00
-- url     : https://prove2.me/submissions/844a4328-5014-4cb0-9465-60740ff1f509

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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennettTwoRowForm_norm_lt
import Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio_bound
import Theorems.Thm_D1Bound5_full_ring_bennettTwoRowForm_exists_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5





/-- The manuscript's two-anchor Bennett inequality for actual roots in
the full integer ring of an imaginary quadratic field. Nonsingularity,
integrality, the norm lower bound, both approximation bounds, and the
nonzero terminal root are derived, not supplied as certificates. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b c d rA rB vA vB z : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hab : a ≠ b)
    (hrA : rA ^ 2 = a * c + 1) (hrB : rB ^ 2 = b * c + 1)
    (hvA : vA ^ 2 = a * d + 1) (hvB : vB ^ 2 = b * d + 1)
    (hzsq : z ^ 2 = c * d + 1)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hAC : 1000 ≤ ‖phi (a : K)‖ * ‖phi (c : K)‖)
    (hC : 4 * ‖phi (b : K)‖ < ‖phi (c : K)‖)
    (k : ℕ) (hk : 1 ≤ k) :
    1 < 3 * ‖phi (c : K)‖ * (42 * ‖phi (b : K)‖ ^ 3 * ‖phi (c : K)‖) ^ k /
        (‖phi (b : K)‖ * ‖phi (z : K)‖) +
      ‖phi (z : K)‖ / (2 * (bennettTwoResidualRate
        ‖phi (a : K)‖ ‖phi (b : K)‖ ‖phi (c : K)‖
          ‖phi (a : K) - phi (b : K)‖) ^ k) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hnonzero (x : 𝓞 K) (hx : x ≠ 0) : f x ≠ 0 := by
    intro h
    apply hx
    apply hf
    simpa only [map_zero] using h
  have ha' := hnonzero a ha
  have hb' := hnonzero b hb
  have hc' := hnonzero c hc
  have hab' : f a ≠ f b := fun h => hab (hf h)
  change ‖f a‖ ≤ ‖f b‖ at hAB
  change 1000 ≤ ‖f a‖ * ‖f c‖ at hAC
  change 4 * ‖f b‖ < ‖f c‖ at hC
  have hz : z ≠ 0 := by
    intro hz0
    have hzC : (f z) ^ 2 = f c * f d + 1 := by
      simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hzsq
    rw [hz0, map_zero, zero_pow (by decide : 2 ≠ 0)] at hzC
    have hcd : f c * f d = -1 := by linear_combination -hzC
    have hnorm : ‖f c‖ * ‖f d‖ = 1 := by
      rw [← norm_mul, hcd]
      norm_num
    have hB1 : 1 ≤ ‖f b‖ := one_le_norm_integer hK phi hb
    have hD1 : 1 ≤ ‖f d‖ := one_le_norm_integer hK phi hd
    have hmul := mul_le_mul_of_nonneg_left hD1 (norm_nonneg (f c))
    nlinarith only [hC, hB1, hnorm, hmul]
  have hz' := hnonzero z hz
  have hBC : 1000 ≤ ‖f b‖ * ‖f c‖ :=
    hAC.trans (mul_le_mul_of_nonneg_right hAB (norm_nonneg (f c)))
  have hCa : 4 * ‖f a‖ < ‖f c‖ := by linarith
  obtain ⟨sA, _, herrorA⟩ := bennett_exists_integral_root_ratio_bound
    f a c d z rA vA ha' hc' hz' hrA hvA hzsq hAC hCa.le
  obtain ⟨sB, _, herrorB⟩ := bennett_exists_integral_root_ratio_bound
    f b c d z rB vB hb' hc' hz' hrB hvB hzsq hBC hC.le
  obtain ⟨i, hi⟩ := full_ring_bennettTwoRowForm_exists_one_le_norm
    hK phi a b c z sA sB ha hb hab hz k hk
  change 1 ≤ ‖bennettTwoRowForm (f a) (f b) (f c) (f z) (f sA) (f sB) k i‖ at hi
  exact hi.trans_lt (bennettTwoRowForm_norm_lt (f a) (f b) (f c) (f z) (f sA) (f sB)
    ha' hb' hc' hab' hz' hAB hAC herrorA herrorB k hk i)

end D1Bound5
end
