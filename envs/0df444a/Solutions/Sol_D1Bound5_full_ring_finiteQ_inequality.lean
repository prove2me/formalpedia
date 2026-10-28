-- Prove2me | solution 1 for D1Bound5.full_ring_finiteQ_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:38:04.056979+00:00
-- url     : https://prove2.me/submissions/cb9cd6ab-e884-42f1-8a96-b2cad7c81509

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteQRowBound_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_bennett_exists_integral_root_ratio_bound
import Theorems.Thm_D1Bound5_finiteQRowForm_norm_lt
import Theorems.Thm_D1Bound5_full_ring_finiteQRowForm_exists_one_le_norm

section
open scoped NumberField
open Module

namespace D1Bound5

/-- The actual finite Q family on six distinct full-ring tuple entries
gives its numerical form inequality. Root signs, a nonzero row, integrality,
height, and the convergent residual estimate are all obtained in the proof. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (a : Fin 4 → 𝓞 K) (c d : 𝓞 K)
    (haS : ∀ j, a j ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hinj : Function.Injective a) (hac : ∀ j, a j ≠ c)
    (had : ∀ j, a j ≠ d) (hcd : c ≠ d)
    (A T : ℝ) (hA : 0 < A)
    (hlower : ∀ j, A ≤ ‖phi (a j : K)‖)
    (hupper : ∀ j, ‖phi (a j : K)‖ ≤ T)
    (hCT : 4*T ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (hAC : 1000 ≤ A*‖phi (c : K)‖) :
    ∃ z : 𝓞 K, z^2 = c*d+1 ∧
      1 < 55*T^3*‖phi (c : K)‖^2/‖phi (z : K)‖ +
        3*T*‖phi (z : K)‖/(2*A^2*‖phi (c : K)‖^4) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hnonzero (x : 𝓞 K) (hx : x ∈ S) : f x ≠ 0 := by
    intro h
    apply hS.1 x hx
    apply hf
    simpa only [map_zero] using h
  have ha0 (j : Fin 4) : f (a j) ≠ 0 := hnonzero (a j) (haS j)
  have hc0 : f c ≠ 0 := hnonzero c hcS
  have hT : 0 < T := (hA.trans_le (hlower 0)).trans_le (hupper 0)
  have hAT : A ≤ T := (hlower 0).trans (hupper 0)
  have hAD : A ≤ ‖f d‖ := by change A ≤ ‖phi (d : K)‖; linarith
  have hCDlarge : 1000 ≤ ‖f c‖*‖f d‖ := by
    have hm := mul_le_mul_of_nonneg_right hAD (norm_nonneg (f c))
    change 1000 ≤ A*‖f c‖ at hAC
    nlinarith only [hAC, hm]
  obtain ⟨z, hz⟩ := hS.2 c hcS d hdS hcd
  have hzsq : z^2 = c*d+1 := by simpa only [pow_two] using hz
  have hzC : (f z)^2 = f c*f d+1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hzsq
  have hz0 : f z ≠ 0 := by
    intro hzero
    have heq : f c*f d = -(1 : ℂ) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hzC.symm
    have hn := congrArg norm heq
    simp only [norm_mul, norm_neg, norm_one] at hn
    linarith
  have hzR : z ≠ 0 := by intro hzero; apply hz0; rw [hzero, map_zero]
  choose r hr using fun j => hS.2 (a j) (haS j) c hcS (hac j)
  choose v hv using fun j => hS.2 (a j) (haS j) d hdS (had j)
  have hrpow (j : Fin 4) : (r j)^2 = a j*c+1 := by simpa only [pow_two] using hr j
  have hvpow (j : Fin 4) : (v j)^2 = a j*d+1 := by simpa only [pow_two] using hv j
  have hACj (j : Fin 4) : 1000 ≤ ‖f (a j)‖*‖f c‖ :=
    hAC.trans (mul_le_mul_of_nonneg_right (hlower j) (norm_nonneg (f c)))
  have hCj (j : Fin 4) : 4*‖f (a j)‖ ≤ ‖f c‖ :=
    (mul_le_mul_of_nonneg_left (hupper j) (by norm_num)).trans hCT
  choose sigma hsigma herr using fun j =>
    bennett_exists_integral_root_ratio_bound f (a j) c d z (r j) (v j)
      (ha0 j) hc0 hz0 (hrpow j) (hvpow j) hzsq (hACj j) (hCj j)
  have hne (i j : Fin 4) (hij : i ≠ j) : a i ≠ a j := fun h => hij (hinj h)
  obtain ⟨i, hL⟩ := full_ring_finiteQRowForm_exists_one_le_norm hK phi
    (a 0) (a 1) (a 2) (a 3) c z (sigma 0) (sigma 1) (sigma 2) (sigma 3)
    (hS.1 _ (haS 0)) (hS.1 _ (haS 1)) (hS.1 _ (haS 2)) (hS.1 _ (haS 3))
    (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide)) hzR
  have hanchor (j : Fin 4) :
      finiteQAnchors (f (a 0)) (f (a 1)) (f (a 2)) (f (a 3)) j = f (a j) := by
    fin_cases j <;> rfl
  have hroot (j : Fin 4) :
      ![f (sigma 0),f (sigma 1),f (sigma 2),f (sigma 3)] j = f (sigma j) := by
    fin_cases j <;> rfl
  have hbound := finiteQRowForm_norm_lt
    (f (a 0)) (f (a 1)) (f (a 2)) (f (a 3)) (f c) (f z)
    (f (sigma 0)) (f (sigma 1)) (f (sigma 2)) (f (sigma 3)) A T hA hz0
    (fun j => by rw [hanchor]; exact hlower j)
    (fun j => by rw [hanchor]; exact hupper j) hAC
    (fun j => by rw [hanchor, hroot]; exact (herr j).le) i
  have hcoeff : 0 < T^3*‖f c‖^2/‖f z‖ := by
    exact div_pos (mul_pos (pow_pos hT 3) (pow_pos (norm_pos_iff.mpr hc0) 2))
      (norm_pos_iff.mpr hz0)
  refine ⟨z, hzsq, ?_⟩
  change 1 < 55*T^3*‖f c‖^2/‖f z‖+3*T*‖f z‖/(2*A^2*‖f c‖^4)
  change 1 ≤ ‖finiteQRowForm
    (f (a 0)) (f (a 1)) (f (a 2)) (f (a 3)) (f c) (f z)
    (f (sigma 0)) (f (sigma 1)) (f (sigma 2)) (f (sigma 3)) i‖ at hL
  calc
    1 < 54*T^3*‖f c‖^2/‖f z‖+3*T*‖f z‖/(2*A^2*‖f c‖^4) :=
      hL.trans_lt hbound
    _ < (54*T^3*‖f c‖^2/‖f z‖+3*T*‖f z‖/(2*A^2*‖f c‖^4)) +
        T^3*‖f c‖^2/‖f z‖ := lt_add_of_pos_right _ hcoeff
    _ = 55*T^3*‖f c‖^2/‖f z‖+3*T*‖f z‖/(2*A^2*‖f c‖^4) := by ring

end D1Bound5
end
