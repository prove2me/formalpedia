-- Prove2me | solution 1 for D1Bound5.full_ring_coherent_two_strong_gap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:23:04.956204+00:00
-- url     : https://prove2.me/submissions/378c9828-86ef-4d04-b563-e02af31c0ec0

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherentQuotientForm_two_eq
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_two_norm_lt
import Theorems.Thm_D1Bound5_coherent_two_strong_gap_scalar
import Theorems.Thm_D1Bound5_full_ring_coherent_two_nonzero_and_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5





/-- The strong two-anchor gap for genuine entries of the full ring of
integers.  Nonvanishing, coefficient integrality, coherent branch bounds,
the complete homogeneous tail, and the integral modulus lower bound
are all discharged by the proved preceding results. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {a b p q : 𝓞 K}
    (ha : a ∈ T) (hb : b ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hab : a ≠ b) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hB : 3 ≤ ‖phi (b : K)‖) (hP : 5 * ‖phi (b : K)‖ ≤ ‖phi (p : K)‖)
    (hAP : 32 ≤ ‖phi (a : K)‖ * ‖phi (p : K)‖)
    (hQ : 5 * ‖phi (a : K)‖ * ‖phi (b : K)‖ * ‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hPQ : 10000 < ‖phi (p : K)‖ * ‖phi (q : K)‖) :
    ‖phi (a : K)‖ ^ 2 * ‖phi (p : K)‖ ^ 3 <
      (10001 / 10000 : ℝ) * ‖phi (q : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  let av : Fin 2 → ℂ := ![f a, f b]
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hinj : Function.Injective av := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hab (hf hij))
    · exact False.elim (hab (hf hij.symm))
    · rfl
  have hA : 1 ≤ ‖f a‖ := one_le_norm_integer hK phi (hT.1 a ha)
  have hA0 : 0 < ‖f a‖ := by linarith
  have hP0 : 0 < ‖f p‖ := by change 0 < ‖phi (p : K)‖; nlinarith only [hB, hP]
  have hQ0 : 0 < ‖f q‖ := by
    have h := one_le_norm_integer hK phi (hT.1 q hq)
    change 0 < ‖phi (q : K)‖
    linarith
  have hQ4 : 4 * ‖f p‖ ≤ ‖f q‖ := by
    have hB' : 3 ≤ ‖f b‖ := hB
    have hQ' : 5*‖f a‖*‖f b‖*‖f p‖ ≤ ‖f q‖ := hQ
    have hAB3 : 3 ≤ ‖f a‖ * ‖f b‖ := by
      have h := mul_le_mul hA hB' (by norm_num : (0 : ℝ) ≤ 3) hA0.le
      simpa only [one_mul] using h
    have h := mul_le_mul_of_nonneg_right hAB3 hP0.le
    nlinarith only [h, hQ', hP0]
  have hlow := (full_ring_coherent_two_nonzero_and_one_le_norm hK phi hT
    a b p q ha hb hp hq hab hap haq hbp hbq hpq eta heta hB hP hQ).2
  have hupp := coherent_two_norm_lt av (f p) (f q) eta hinj hA0 hP0 hAB
    hAP hQ4 hPQ heta
  rw [coherentQuotientForm_two_eq av hinj] at hupp
  have hbound : 1 < 21 * ‖f b‖ / (20 * ‖coherentTerminalRoot (f p) (f q) eta‖) +
      ‖coherentTerminalRoot (f p) (f q) eta‖ / (2 * ‖f a‖ * ‖f p‖ ^ 2) := by
    exact hlow.trans_lt hupp
  have hzsq : (coherentTerminalRoot (f p) (f q) eta) ^ 2 = f p * f q + 1 :=
    coherent_analytic_terminal_root_sq (f p) (f q) eta
      (norm_pos_iff.mp hP0) (norm_pos_iff.mp hQ0) heta
  have hnorm : ‖coherentTerminalRoot (f p) (f q) eta‖ ^ 2 = ‖f p * f q + 1‖ := by
    simpa only [norm_pow] using congrArg norm hzsq
  have hZupper : ‖coherentTerminalRoot (f p) (f q) eta‖ ^ 2 ≤ ‖f p‖ * ‖f q‖ + 1 := by
    rw [hnorm]
    simpa only [norm_mul, norm_one] using norm_add_le (f p * f q) (1 : ℂ)
  have hZlower : ‖f p‖ * ‖f q‖ - 1 ≤ ‖coherentTerminalRoot (f p) (f q) eta‖ ^ 2 := by
    have h := norm_sub_le (f p * f q + 1) (1 : ℂ)
    simp only [add_sub_cancel_right, norm_mul, norm_one, ← hnorm] at h
    linarith
  exact coherent_two_strong_gap_scalar ‖f a‖ ‖f b‖ ‖f p‖ ‖f q‖
    ‖coherentTerminalRoot (f p) (f q) eta‖ hA hB hP hAP hQ hPQ
    (norm_nonneg _) hZlower hZupper hbound

end D1Bound5
end
