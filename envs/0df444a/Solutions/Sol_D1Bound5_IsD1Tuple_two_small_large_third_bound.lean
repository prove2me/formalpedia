-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_large_third_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:13:53.064094+00:00
-- url     : https://prove2.me/submissions/e155a31b-d845-4508-83cc-eb9588063ab7

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.ComputeDegree
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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_four_anchor_V_window
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_growth_inputs
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_ordinary_at
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_ordinaryLog10_div
import Theorems.Thm_D1Bound5_ordinaryLog10_lt_nat_iff
import Theorems.Thm_D1Bound5_ordinaryLog10_mono
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinaryLog10_ten
import Theorems.Thm_D1Bound5_two_small_large_S_eighth_power
import Theorems.Thm_D1Bound5_two_small_large_S_parameters

section
open scoped NumberField
open Module

namespace D1Bound5





theorem twoSmallHeightEnvelope_lt_396 (x : ℝ) (hlo : 8 ≤ x) (hhi : x ≤ 50) :
    twoSmallHeightEnvelope x < 396 := by
  have hx : 0 < x-4 := by linarith only [hlo]
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hnum : (4047/25 : ℝ) < (396-(7*x+212/5))*(x-4) := by
    nlinarith only [hp,hlo,hhi]
  have hd := (div_lt_iff₀ hx).2 hnum
  dsimp [twoSmallHeightEnvelope]
  linarith only [hd]

theorem twoSmallHeightEnvelope_lt_eight_mul_sub_four
    (x : ℝ) (hx : 50 ≤ x) : twoSmallHeightEnvelope x < 8*x-4 := by
  have hr : (4047/25 : ℝ)/(x-4) ≤ (4047/25)/46 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hx])
  dsimp [twoSmallHeightEnvelope]
  norm_num at hr
  linarith only [hr,hx]

/-- The complete large-third-entry branch of the two-small cutoff.
All determinant, interpolation and ordinary height inputs are derived
from the actual ordered sextuple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB3 : ‖phi (a 1 : K)‖ < 3)
    (hS : (10 : ℝ)^8 ≤ ‖phi (a 2 : K)‖) :
    ‖phi (a 2 : K)‖ < (10 : ℝ)^50 ∧ ‖phi (a 5 : K)‖ < (10 : ℝ)^396 := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let T := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let D := ‖f (a 5)‖
  change B < 3 at hB3
  change (10 : ℝ)^8 ≤ S at hS
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hB : 1 ≤ B := one_le_norm_integer hK phi (ha.2.1 1)
  have hS0 : 0 < S := by change (10 : ℝ)^8 ≤ S at hS; norm_num at hS; linarith only [hS]
  have hD0 : 0 < D := hS0.trans_le (hmon (by decide : (2 : Fin 6) ≤ 5))
  have hST : S ≤ T := hmon (by decide : (2 : Fin 6) ≤ 3)
  have hg := ha.two_small_growth_inputs hK phi a hmon (by
    change (10 : ℝ)^8 ≤ S at hS
    norm_num at hS
    change 3 ≤ S
    linarith only [hS])
  have hAT : 9 ≤ A*T := by
    have hh := mul_le_mul_of_nonneg_right hA (show 0 ≤ T from (hS0.trans_le hST).le)
    change (10 : ℝ)^8 ≤ S at hS
    norm_num at hS
    nlinarith only [hh,hST,hS]
  have hp := two_small_large_S_parameters A B S T C D hA hB hB3 hS hST hg.1 hg.2.1 (hg.2.2 hAT)
  have hw := ha.four_anchor_V_window hK phi a hmon hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
  have hV : (2/5 : ℝ)*A^2*C^5/T^2 < D := by
    rcases hw with hw | hw
    · exact False.elim (lt_asymm hw hp.2.2.2.2)
    · exact hw
  have hpower := two_small_large_S_eighth_power A S T C D hA hS0 hST hg.1 hV
  have hupper := ha.two_small_ordinary_at hK phi a hmon hB3 2 (by decide) (by decide) hS
  change ordinaryLog10 D < twoSmallHeightEnvelope (ordinaryLog10 S) at hupper
  have hlower : 8*ordinaryLog10 S-4 < ordinaryLog10 D := by
    have hh := ordinaryLog10_strictMono (by positivity : 0 < S^8/(10 : ℝ)^4) hpower
    rw [ordinaryLog10_div _ _ (by positivity) (by positivity),ordinaryLog10_pow,
      ordinaryLog10_pow,ordinaryLog10_ten] at hh
    norm_num at hh
    exact hh
  have hSsmall : S < (10 : ℝ)^50 := by
    by_contra hbad
    have hx := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^50) (le_of_not_gt hbad)
    simp only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] at hx
    have hh := twoSmallHeightEnvelope_lt_eight_mul_sub_four (ordinaryLog10 S) hx
    linarith only [hlower,hupper,hh]
  have hxlo : 8 ≤ ordinaryLog10 S := by
    have hh := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^8) hS
    simpa only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] using hh
  have hxhi : ordinaryLog10 S < 50 := (ordinaryLog10_lt_nat_iff S hS0 50).2 hSsmall
  have hDsmall : D < (10 : ℝ)^396 := by
    apply (ordinaryLog10_lt_nat_iff D hD0 396).1
    exact hupper.trans (twoSmallHeightEnvelope_lt_396 (ordinaryLog10 S) hxlo hxhi.le)
  exact ⟨hSsmall,hDsmall⟩

end D1Bound5
end
