-- Prove2me | solution 1 for D1Bound5.full_ring_finiteM_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:25:48.149732+00:00
-- url     : https://prove2.me/submissions/ab19c583-e29c-4d0e-a4e0-85a8f2b6c1b8

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteMIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteMRowBound_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio_bound
import Theorems.Thm_D1Bound5_finiteMRowForm_norm_lt
import Theorems.Thm_D1Bound5_full_ring_finiteMRowForm_exists_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual ordinary-three order-two matrix supplies a nonzero
integral form on five distinct D(1) entries, with its explicit height
and residual bounds. No row-selection or root-lifting premise remains. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (a : Fin 3 → 𝓞 K) (c d : 𝓞 K)
    (haS : ∀ j, a j ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hinj : Function.Injective a) (hac : ∀ j, a j ≠ c)
    (had : ∀ j, a j ≠ d) (hcd : c ≠ d)
    (hmon : Monotone (fun j => ‖phi (a j : K)‖))
    (hCT : 4*‖phi (a 2 : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (hAC : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (c : K)‖) :
    ∃ z : 𝓞 K, z^2 = c*d+1 ∧
      1 < (8/9 : ℝ)*608^2*‖phi (a 1 : K)‖^3*‖phi (a 2 : K)‖^8*‖phi (c : K)‖^3/
          ‖phi (z : K)‖+
        (3920/81 : ℝ)*‖phi (a 1 : K)‖^2*‖phi (a 2 : K)‖^5*‖phi (z : K)‖/
          (‖phi (a 0 : K)‖^3*‖phi (c : K)‖^6) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  change Monotone (fun j => ‖f (a j)‖) at hmon
  change 4*‖f (a 2)‖ ≤ ‖f c‖ at hCT
  change ‖f c‖ ≤ ‖f d‖ at hCD
  change 1000 ≤ ‖f (a 0)‖*‖f c‖ at hAC
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hn (x : 𝓞 K) (hx : x ∈ S) : f x ≠ 0 := by
    intro h
    apply hS.1 x hx
    apply hf
    simpa only [map_zero] using h
  have ha0 (j : Fin 3) : f (a j) ≠ 0 := hn (a j) (haS j)
  have hc0 : f c ≠ 0 := hn c hcS
  have hA1 : 1 ≤ ‖f (a 0)‖ := one_le_norm_integer hK phi (hS.1 _ (haS 0))
  have hC1 : 1 ≤ ‖f c‖ := one_le_norm_integer hK phi (hS.1 _ hcS)
  have hAD : ‖f (a 0)‖ ≤ ‖f d‖ := by
    have hh := hmon (by decide : (0 : Fin 3) ≤ 2)
    have ht := norm_nonneg (f (a 2))
    linarith only [hh,ht,hCT,hCD]
  have hCDlarge : 1000 ≤ ‖f c‖*‖f d‖ := by
    have hh := mul_le_mul_of_nonneg_right hAD (norm_nonneg (f c))
    nlinarith only [hAC,hh]
  obtain ⟨z,hz⟩ := hS.2 c hcS d hdS hcd
  have hzsq : z^2 = c*d+1 := by simpa only [pow_two] using hz
  have hzC : (f z)^2 = f c*f d+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hzsq
  have hz0 : f z ≠ 0 := by
    intro hzero
    have heq : f c*f d = -(1 : ℂ) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [hzero,zero_pow (by decide : (2 : ℕ) ≠ 0)] using hzC.symm
    have hh := congrArg norm heq
    simp only [norm_mul,norm_neg,norm_one] at hh
    linarith only [hh,hCDlarge]
  have hzR : z ≠ 0 := by intro hzero; apply hz0; rw [hzero,map_zero]
  choose r hr using fun j => hS.2 (a j) (haS j) c hcS (hac j)
  choose v hv using fun j => hS.2 (a j) (haS j) d hdS (had j)
  have hrpow (j : Fin 3) : (r j)^2 = a j*c+1 := by simpa only [pow_two] using hr j
  have hvpow (j : Fin 3) : (v j)^2 = a j*d+1 := by simpa only [pow_two] using hv j
  have hACj (j : Fin 3) : 1000 ≤ ‖f (a j)‖*‖f c‖ :=
    hAC.trans (mul_le_mul_of_nonneg_right (hmon (Fin.zero_le j)) (norm_nonneg (f c)))
  have hCj (j : Fin 3) : 4*‖f (a j)‖ ≤ ‖f c‖ :=
    (mul_le_mul_of_nonneg_left (hmon (by omega : j ≤ 2)) (by norm_num)).trans hCT
  choose sigma hsigma herr using fun j =>
    bennett_exists_integral_root_ratio_bound f (a j) c d z (r j) (v j)
      (ha0 j) hc0 hz0 (hrpow j) (hvpow j) hzsq (hACj j) (hCj j)
  obtain ⟨i,hL⟩ := full_ring_finiteMRowForm_exists_one_le_norm hK phi
    (a 0) (a 1) (a 2) c z (sigma 0) (sigma 1) (sigma 2)
    (hS.1 _ (haS 0)) (hS.1 _ (haS 1)) (hS.1 _ (haS 2))
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide)) hzR
  have hanchor (j : Fin 3) : finiteMAnchors (f (a 0)) (f (a 1)) (f (a 2)) j = f (a j) := by
    fin_cases j <;> rfl
  have hroot (j : Fin 3) : ![f (sigma 0),f (sigma 1),f (sigma 2)] j = f (sigma j) := by
    fin_cases j <;> rfl
  have hbound := finiteMRowForm_norm_lt (f (a 0)) (f (a 1)) (f (a 2)) (f c) (f z)
    (f (sigma 0)) (f (sigma 1)) (f (sigma 2)) (ha0 0) (ha0 1) (ha0 2) hc0 hz0
    (hf.ne (hinj.ne (by decide))) (hf.ne (hinj.ne (by decide))) (hf.ne (hinj.ne (by decide)))
    hA1 (hmon (by decide)) (hmon (by decide)) hC1 hAC
    (fun j => by rw [hanchor,hroot]; exact (herr j).le) i
  exact ⟨z,hzsq,hL.trans_lt hbound⟩

end D1Bound5
end
