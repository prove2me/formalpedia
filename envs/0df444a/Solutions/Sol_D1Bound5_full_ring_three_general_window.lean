-- Prove2me | solution 1 for D1Bound5.full_ring_three_general_window
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:41:52.181347+00:00
-- url     : https://prove2.me/submissions/1a4c6ee7-ca64-4f60-a2a9-aa3bd36d0faf

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
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_analytic_terminal_root_sq
import Theorems.Thm_D1Bound5_coherent_three_general_norm_lt
import Theorems.Thm_D1Bound5_finite_tuple_root_relative_norm
import Theorems.Thm_D1Bound5_full_ring_coherent_three_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer
import Theorems.Thm_D1Bound5_three_general_window_scalar

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- Nonzero general three-anchor forms in the full integer ring exclude
the general-three window. Integrality is supplied from actual D(1)
entries and the coherent square roots; it is not an external premise. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup) {p q : 𝓞 K}
    (hp : p ∈ Tup) (hq : q ∈ Tup) (hpq : p ≠ q)
    (a : Fin 3 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ Tup) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hP : 4*‖phi (a 2 : K)‖ ≤ ‖phi (p : K)‖)
    (hAP : 9 ≤ ‖phi (a 0 : K)‖*‖phi (p : K)‖)
    (hQ : ‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hPQ : 4000 ≤ ‖phi (p : K)‖*‖phi (q : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (p : K)*phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K))
      (coherentVandermonde3 (fun i => phi (a i : K)))
        (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    ‖phi (q : K)‖ < 101*‖phi (a 1 : K)‖^2*‖phi (a 2 : K)‖^4/‖phi (p : K)‖ ∨
      ‖phi (a 0 : K)‖^2*‖phi (p : K)‖^5/(37*‖phi (a 2 : K)‖^2) < ‖phi (q : K)‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  change 4*‖f (a 2)‖ ≤ ‖f p‖ at hP
  change 4000 ≤ ‖f p‖*‖f q‖ at hPQ
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hn (i : Fin 3) : 0 < ‖f (a i)‖ := by
    have hh := one_le_norm_integer hK phi (hTup.1 _ (ha i))
    change 1 ≤ ‖f (a i)‖ at hh
    linarith only [hh]
  have hp0 : 0 < ‖f p‖ := by have hh := hn 2; linarith only [hP,hh]
  have hq0 : 0 < ‖f q‖ := hp0.trans_le hQ
  have hdelta : phi ((coherentVandermonde3 a : 𝓞 K) : K) =
      coherentVandermonde3 (fun i => phi (a i : K)) := by
    change f (coherentVandermonde3 a) = coherentVandermonde3 (fun i => f (a i))
    simp [coherentVandermonde3]
  have hL' : coherentQuotientForm (fun i => phi (a i : K))
      (phi ((coherentVandermonde3 a : 𝓞 K) : K))
        (phi (p : K)) (phi (q : K)) eta ≠ 0 := by rwa [hdelta]
  have hlower := full_ring_coherent_three_one_le_norm hK phi hTup hp hq hpq
    a hinj ha hap haq eta heta hL'
  rw [hdelta] at hlower
  have hupper := coherent_three_general_norm_lt (fun i => f (a i))
    (f p) (f q) eta (hf.comp hinj) (hn 0) hAB hBS hP hAP hQ heta
  let z := coherentTerminalRoot (f p) (f q) eta
  have hz : z^2 = f p*f q+1 := coherent_analytic_terminal_root_sq (f p) (f q) eta
    (norm_pos_iff.mp hp0) (norm_pos_iff.mp hq0) heta
  have hrel := finite_tuple_root_relative_norm (f p) (f q) z hz hPQ
  have hZ : 0 < ‖z‖ := by
    have hh := hrel.1
    have hn := norm_nonneg z
    nlinarith only [hh,hPQ,hn]
  exact three_general_window_scalar ‖f (a 0)‖ ‖f (a 1)‖ ‖f (a 2)‖
    ‖f p‖ ‖f q‖ ‖z‖ (hn 0) (hn 1) (hn 2) hp0 hZ hrel.1 hrel.2
    (hlower.trans_lt hupper)

end D1Bound5
end
