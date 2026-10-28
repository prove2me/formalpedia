-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.two_small_ordinary_height
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:26:27.206977+00:00
-- url     : https://prove2.me/submissions/de0b0180-a843-453a-a434-8ecb0b71bce7

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
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_height_envelope
import Theorems.Thm_D1Bound5_bennettTwoResidualRate_norm_lower
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_ordinaryLog10_mono
import Theorems.Thm_D1Bound5_ordinaryLog10_mul
import Theorems.Thm_D1Bound5_ordinaryLog10_pow
import Theorems.Thm_D1Bound5_ordinaryLog10_strictMono
import Theorems.Thm_D1Bound5_ordinaryLog10_ten
import Theorems.Thm_D1Bound5_ordinaryLog10_two_small_parameters

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The uniform ordinary height bound for two small anchors, derived
from the actual integral Bennett rows of the given quadruple. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 4 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hB : ‖phi (a 1 : K)‖ < 3)
    (hP : (10 : ℝ)^8 ≤ ‖phi (a 2 : K)‖) :
    ordinaryLog10 ‖phi (a 3 : K)‖ <
      twoSmallHeightEnvelope (ordinaryLog10 ‖phi (a 2 : K)‖) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let A := ‖f (a 0)‖
  let B := ‖f (a 1)‖
  let P := ‖f (a 2)‖
  change (10 : ℝ)^8 ≤ P at hP
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hA1 : 1 ≤ A := one_le_norm_integer hK phi (ha.2.1 0)
  have hB1 : 1 ≤ B := one_le_norm_integer hK phi (ha.2.1 1)
  have hA0 : 0 < A := by linarith only [hA1]
  have hB0 : 0 < B := by linarith only [hB1]
  have hP0 : 0 < P := (by norm_num : (0 : ℝ) < 10^8).trans_le hP
  have hB3 : B < 3 := hB
  have hAP : 1000 ≤ A*P := by
    have hh := mul_le_mul_of_nonneg_right hA1 hP0.le
    change (10 : ℝ)^8 ≤ P at hP
    norm_num at hP
    nlinarith only [hh,hP]
  have hPB : 4*B < P := by
    change (10 : ℝ)^8 ≤ P at hP
    norm_num at hP
    linarith only [hB3,hP]
  have hx : 8 ≤ ordinaryLog10 P := by
    have hh := ordinaryLog10_mono (by positivity : (0 : ℝ) < 10^8) hP
    simpa only [ordinaryLog10_pow,ordinaryLog10_ten,Nat.cast_ofNat,mul_one] using hh
  obtain ⟨hHconst,hRconst,hUconst⟩ := ordinaryLog10_two_small_parameters
  have hHlt : 42*B^3*P < 1134*P := by
    have hb3 : B^3 < (3 : ℝ)^3 := by gcongr
    have hh := mul_lt_mul_of_pos_right hb3 (by positivity : 0 < 42*P)
    nlinarith only [hh]
  have hHlog : ordinaryLog10 (42*B^3*P) < ordinaryLog10 P+31/10 := by
    have hh := ordinaryLog10_strictMono (by positivity : 0 < 42*B^3*P) hHlt
    rw [ordinaryLog10_mul 1134 P (by norm_num) hP0.ne'] at hh
    linarith only [hh,hHconst]
  have hUlog : ordinaryLog10 (253*B^2) < (17/5 : ℝ) := by
    have hb2 : B^2 < (3 : ℝ)^2 := by gcongr
    have hlt : 253*B^2 < 2277 := by nlinarith only [hb2]
    exact (ordinaryLog10_strictMono (by positivity : 0 < 253*B^2) hlt).trans hUconst
  have hrate := bennettTwoResidualRate_norm_lower (f (a 0)) (f (a 1)) (f (a 2))
    (norm_pos_iff.mp hA0) (norm_pos_iff.mp hB0)
    (hf.ne (ha.1.ne (by decide : (0 : Fin 4) ≠ 1)))
    (hmon (by decide : (0 : Fin 4) ≤ 1)) hAP
  have hsimple : (2/15 : ℝ)*P^2 < 2*A*P^2/(5*B) := by
    apply (lt_div_iff₀ (by positivity : 0 < 5*B)).2
    have hAB : B < 3*A := by linarith only [hB3,hA1]
    have hh := mul_lt_mul_of_pos_right hAB (sq_pos_of_pos hP0)
    nlinarith only [hh]
  have hRlog : 2*ordinaryLog10 P-9/10 <
      ordinaryLog10 (bennettTwoResidualRate A B P ‖f (a 0)-f (a 1)‖) := by
    have hh := ordinaryLog10_strictMono (by positivity : 0 < (2/15 : ℝ)*P^2)
      (hsimple.trans hrate)
    rw [ordinaryLog10_mul (2/15) (P^2) (by norm_num) (by positivity),
      ordinaryLog10_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh,hRconst]
  have hout := ha.ordinary_height_envelope hK phi a hmon hAP hPB
    (31/10) (-(9/10)) (17/5) hHlog
    (by
      change 2*ordinaryLog10 P+-(9/10) <
        ordinaryLog10 (bennettTwoResidualRate A B P ‖f (a 0)-f (a 1)‖)
      simpa only [sub_eq_add_neg] using hRlog) hUlog
    (by
      change (31/10 : ℝ)-(-(9/10)) < ordinaryLog10 P
      linarith only [hx])
    (by
      change 0 < 2*ordinaryLog10 P+-(9/10)
      linarith only [hx])
  convert hout using 1 <;> dsimp [twoSmallHeightEnvelope] <;> norm_num <;> ring

end D1Bound5
end
