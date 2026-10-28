-- Prove2me | solution 1 for D1Bound5.full_ring_finiteN3Bs_fixed_interval_excluded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:03:57.215304+00:00
-- url     : https://prove2.me/submissions/07817abc-483d-4621-9a95-6f7ddbe01c74

import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteN3FixedHeight_Definitions
import Definitions.Def_D1Bound5_FiniteN3Matrix_Definitions
import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_finiteN3_fixed_height
import Theorems.Thm_D1Bound5_fixed_n3_bs_adaptive_bound
import Theorems.Thm_D1Bound5_full_ring_finiteN3_exact_interval_of_bounds
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_finiteN3BsFixedBound
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_valid
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_norm
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_sub

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



/-- The actual fixed-table N3bs interval. The numerator B⁸ in the upper
endpoint is retained, as required by the next overlap in the manuscript. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {U : Finset (𝓞 K)} (hU : IsD1 U) (b s c d : 𝓞 K)
    (hbU : b ∈ U) (hsU : s ∈ U) (hcU : c ∈ U) (hdU : d ∈ U)
    (hbs : b ≠ s) (hbc : b ≠ c) (hsc : s ≠ c)
    (hbd : b ≠ d) (hsd : s ≠ d) (hcd : c ≠ d)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC1000 : 1000 ≤ ‖phi (c : K)‖)
    (hCS : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (r : OneSmallCutoffRow) (hr : r ∈ oneSmallCutoffRows)
    (e : QuadInt r.triple.tau r.triple.nu ≃+* 𝓞 K)
    (sgn conj : Bool)
    (hb : smallExtensionSymmetry sgn conj (e.symm b) = r.triple.anchorB)
    (hs : smallExtensionSymmetry sgn conj (e.symm s) = r.triple.anchorS)
    (hleft : 4*(r.Mbs : ℝ)^2*‖phi (s : K)‖^14*‖phi (c : K)‖^7/
      (1-1/4000 : ℝ) ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤ ‖phi (b : K)‖^8*‖phi (c : K)‖^11/
      (4*(r.Rbs : ℝ)^2*‖phi (s : K)‖^6*(1+1/4000 : ℝ))) : False := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let B := ‖f b‖
  let S := ‖f s‖
  let delta := ‖f b-f s‖
  have hB1 : 1 ≤ B := one_le_norm_integer hK phi (hU.1 b hbU)
  have hB : 0 < B := by linarith only [hB1]
  have hS : 0 < S := hB.trans_le hBS
  have hfi : Function.Injective f := by
    intro x y h
    apply NumberField.RingOfIntegers.ext
    exact phi.injective h
  have hd : 0 < delta := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hbs (hfi h)))
  have hnorm (w : 𝓞 K) : ‖f w‖^2 =
      ((smallExtensionSymmetry sgn conj (e.symm w)).norm : ℝ) := by
    change ‖phi (w : K)‖^2 =
      ((smallExtensionSymmetry sgn conj (e.symm w)).norm : ℝ)
    simpa only [smallExtensionSymmetry_norm,RingEquiv.apply_symm_apply] using
      norm_sq_full_ring_equiv e phi (e.symm w)
  have hBsq : B^2 = (r.b0 : ℝ) := by
    have hh := hnorm b
    rw [hb] at hh
    simpa [OneSmallCutoffRow.b0] using hh
  have hSsq : S^2 = (r.s0 : ℝ) := by
    have hh := hnorm s
    rw [hs] at hh
    simpa [OneSmallCutoffRow.s0] using hh
  have hdsq : delta^2 = (r.dbs : ℝ) := by
    have hh := hnorm (b-s)
    simp only [map_sub,smallExtensionSymmetry_sub,hb,hs] at hh
    simpa [delta,OneSmallCutoffRow.dbs] using hh
  obtain ⟨_,_,_,_,_,_,_,_,hphi,hphi6,hphi5,_,_,_,_,_,_,_,hMbs,_⟩ :=
    oneSmallCutoffRows_valid r hr
  have hF : 0 ≤ (r.phi1 : ℝ) := by exact_mod_cast hphi
  have h6 : delta^12/S^12 ≤ (r.phi1 : ℝ)^2 := by
    have hh : (r.dbs : ℝ)^6/(r.s0 : ℝ)^6 ≤ (r.phi1 : ℝ)^2 := by
      exact_mod_cast hphi6
    rw [←hdsq,←hSsq] at hh
    convert hh using 1 <;> ring
  have h5 : B^2*delta^10/S^12 ≤ (r.phi1 : ℝ)^2 := by
    have hh : (r.b0 : ℝ)*(r.dbs : ℝ)^5/(r.s0 : ℝ)^6 ≤ (r.phi1 : ℝ)^2 := by
      exact_mod_cast hphi5
    rw [←hBsq,←hdsq,←hSsq] at hh
    convert hh using 1 <;> ring
  obtain ⟨hFpos,hmax⟩ := fixed_n3_bs_adaptive_bound B S delta (r.phi1 : ℝ) hB.le hS hd hF h6 h5
  have hReq : (r.Rbs : ℝ) = (3535/409600 : ℝ)*(r.phi1 : ℝ) := by
    simp only [OneSmallCutoffRow.Rbs]
    push_cast
    <;> rfl
  have hRpos : 0 < (r.Rbs : ℝ) := by rw [hReq]; positivity
  have hR : (3535/409600 : ℝ)*max (delta^6) (B*delta^5) ≤ (r.Rbs : ℝ)*S^6 := by
    rw [hReq]
    have hh := mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 3535/409600)
    simpa only [mul_assoc] using hh
  have hM : 0 < (r.Mbs : ℝ) := by exact_mod_cast hMbs
  obtain ⟨w,hw⟩ := oneSmallCutoffRows_finiteN3BsFixedBound r hr
  have hheight (i : Fin 3) := finiteN3_fixed_height phi r.triple.anchorB r.triple.anchorS
    r.Mbs w hw e sgn conj b s c hb hs (norm_pos_iff.mp hS) hC1000 hCS i
  exact full_ring_finiteN3_exact_interval_of_bounds hK phi hU b s c d
    hbU hsU hcU hdU hbs hbc hsc hbd hsd hcd hBS hC1000 hCS hCD
    (r.Mbs : ℝ) (r.Rbs : ℝ) hM hRpos hheight hR hleft hright

end D1Bound5
end
