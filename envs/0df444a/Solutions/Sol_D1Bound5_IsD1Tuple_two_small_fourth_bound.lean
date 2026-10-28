-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:07:49.690603+00:00
-- url     : https://prove2.me/submissions/a4a14e5a-50f0-4bc3-a28a-aa13552fff0d

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
import Theorems.Thm_D1Bound5_IsD1Tuple_comp_injective_map
import Theorems.Thm_D1Bound5_IsD1Tuple_four_anchor_V_window
import Theorems.Thm_D1Bound5_IsD1Tuple_three_anchor_general_alternative
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_growth_inputs
import Theorems.Thm_D1Bound5_IsD1Tuple_two_small_ordinary_at
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_ordinaryLog10_div
import Theorems.Thm_D1Bound5_ordinaryLog10_lt_nat_iff
import Theorems.Thm_D1Bound5_ordinaryLog10_mono
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinaryLog10_ten
import Theorems.Thm_D1Bound5_two_small_large_T_lower_window_impossible
import Theorems.Thm_D1Bound5_two_small_large_T_quadratic_eighth
import Theorems.Thm_D1Bound5_two_small_large_T_quadratic_parameters
import Theorems.Thm_D1Bound5_two_small_large_T_quintic_eighth

section
namespace D1Bound5





theorem twoSmallHeightEnvelope_lt_549 (x : ℝ) (hlo : 8 ≤ x) (hhi : x ≤ 72) :
    twoSmallHeightEnvelope x < 549 := by
  have hx : 0 < x-4 := by linarith only [hlo]
  have hp := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hnum : (4047/25 : ℝ) < (549-(7*x+212/5))*(x-4) := by
    nlinarith only [hp,hlo,hhi]
  have hd := (div_lt_iff₀ hx).2 hnum
  dsimp [twoSmallHeightEnvelope]
  linarith only [hd]



theorem twoSmallHeightEnvelope_lt_eight_mul_sub_twenty_seven
    (x : ℝ) (hx : 72 ≤ x) : twoSmallHeightEnvelope x < 8*x-27 := by
  have hr : (4047/25 : ℝ)/(x-4) ≤ (4047/25)/68 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hx])
  dsimp [twoSmallHeightEnvelope]
  norm_num at hr
  linarith only [hr,hx]





end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The fourth-entry bound in the branch where the third entry is below
10^8. The zero and nonzero coherent-form cases are both derived from
the actual quintuple restriction, before the ordinary height contradiction. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB3 : ‖phi (a 1 : K)‖ < 3) (hS3 : 3 ≤ ‖phi (a 2 : K)‖)
    (hS8 : ‖phi (a 2 : K)‖ < (10 : ℝ)^8) :
    ‖phi (a 3 : K)‖ < (10 : ℝ)^72 ∧
      ((10 : ℝ)^8 ≤ ‖phi (a 3 : K)‖ → ‖phi (a 5 : K)‖ < (10 : ℝ)^549) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let S := ‖f (a 2)‖
  let T := ‖f (a 3)‖
  let C := ‖f (a 4)‖
  let D := ‖f (a 5)‖
  change B < 3 at hB3
  change 3 ≤ S at hS3
  change S < (10 : ℝ)^8 at hS8
  have hA : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hB : 1 ≤ B := one_le_norm_integer hK phi (ha.2.1 1)
  have hB0 : 0 < B := by linarith only [hB]
  have hS0 : 0 < S := by linarith only [hS3]
  have hT0 : 0 < T := hS0.trans_le (hmon (by decide : (2 : Fin 6) ≤ 3))
  have hD0 : 0 < D := hT0.trans_le (hmon (by decide : (3 : Fin 6) ≤ 5))
  have hg := ha.two_small_growth_inputs hK phi a hmon hS3
  have hTsmall : T < (10 : ℝ)^72 := by
    by_contra hbad
    have hTbig : (10 : ℝ)^72 ≤ T := le_of_not_gt hbad
    have hT8 : (10 : ℝ)^8 ≤ T := by norm_num at hTbig ⊢; linarith only [hTbig]
    have hAT : 9 ≤ A*T := by
      have hh := mul_le_mul_of_nonneg_right hA hT0.le
      norm_num at hTbig
      nlinarith only [hh,hTbig]
    let e : Fin 5 → Fin 6 := ![0,1,2,3,4]
    have he : Function.Injective e := by decide
    have hb := ha.comp_injective_map a e he
    have hbmon : Monotone (fun i => ‖f (a (e i))‖) := by
      have hidx : Monotone e := by decide
      exact fun i j hij => hmon (hidx hij)
    have hT1000 : 1000 ≤ T := by norm_num at hTbig; linarith only [hTbig]
    have hST4 : 4*S ≤ T := by
      norm_num at hS8 hTbig
      linarith only [hS8,hTbig]
    have halt := hb.three_anchor_general_alternative hK phi (fun i => a (e i))
      hbmon hT1000 hST4
    have hpower : T^8/(10 : ℝ)^27 < D := by
      rcases halt with hquad | hlow | hquintic
      · have hp := two_small_large_T_quadratic_parameters A B S T C D
          hA hB hB3 hS3 hTbig hquad hg.2.1
        have hw := ha.four_anchor_V_window hK phi a hmon hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
        have hV : (2/5 : ℝ)*A^2*C^5/T^2 < D := by
          rcases hw with hw | hw
          · exact False.elim (lt_asymm hw hp.2.2.2.2)
          · exact hw
        have hh := two_small_large_T_quadratic_eighth A B S T C D hA hB hS3 hT0 hquad hV
        apply lt_trans _ hh
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 10^27)).2
        norm_num
        nlinarith only [pow_pos hT0 8]
      · exact False.elim (two_small_large_T_lower_window_impossible B S T C
          hB0 hB3 hS0 hS8 hTbig (hmon (by decide : (3 : Fin 6) ≤ 4)) hlow)
      · exact two_small_large_T_quintic_eighth A B S T C D hA hB hS0 hS8 hT0
          hquintic (hg.2.2 hAT)
    have hlower : 8*ordinaryLog10 T-27 < ordinaryLog10 D := by
      have hh := ordinaryLog10_strictMono (by positivity : 0 < T^8/(10 : ℝ)^27) hpower
      rw [ordinaryLog10_div _ _ (by positivity) (by positivity),ordinaryLog10_pow,
        ordinaryLog10_pow,ordinaryLog10_ten] at hh
      norm_num at hh
      exact hh
    have hupper := ha.two_small_ordinary_at hK phi a hmon hB3 3 (by decide) (by decide) hT8
    change ordinaryLog10 D < twoSmallHeightEnvelope (ordinaryLog10 T) at hupper
    have hx : 72 ≤ ordinaryLog10 T := by
      have hh := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^72) hTbig
      simpa only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] using hh
    have hh := twoSmallHeightEnvelope_lt_eight_mul_sub_twenty_seven (ordinaryLog10 T) hx
    linarith only [hlower,hupper,hh]
  refine ⟨hTsmall,?_⟩
  intro hT8
  change (10 : ℝ)^8 ≤ T at hT8
  have hupper := ha.two_small_ordinary_at hK phi a hmon hB3 3 (by decide) (by decide) hT8
  change ordinaryLog10 D < twoSmallHeightEnvelope (ordinaryLog10 T) at hupper
  have hxlo : 8 ≤ ordinaryLog10 T := by
    have hh := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^8) hT8
    simpa only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] using hh
  have hxhi : ordinaryLog10 T < 72 := (ordinaryLog10_lt_nat_iff T hT0 72).2 hTsmall
  apply (ordinaryLog10_lt_nat_iff D hD0 549).1
  exact hupper.trans (twoSmallHeightEnvelope_lt_549 (ordinaryLog10 T) hxlo hxhi.le)

end D1Bound5
end
