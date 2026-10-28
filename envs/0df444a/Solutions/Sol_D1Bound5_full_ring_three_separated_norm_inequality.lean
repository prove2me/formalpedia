-- Prove2me | solution 1 for D1Bound5.full_ring_three_separated_norm_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:52:57.770919+00:00
-- url     : https://prove2.me/submissions/71dc743a-01df-4db6-8335-c27f1c130bbb

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
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_coherent_three_separated_bounds
import Theorems.Thm_D1Bound5_full_ring_coherent_three_one_le_norm
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5

/-- The separated three-anchor inequality for actual integral entries.
Only the vanishing decision is left to a subsequent four-anchor lemma. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup) {p q : 𝓞 K}
    (hp : p ∈ Tup) (hq : q ∈ Tup) (hpq : p ≠ q)
    (a : Fin 3 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ Tup) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hP : 0 < ‖phi (p : K)‖) (hAP : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (p : K)‖)
    (hQ : 4*‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hPQ : 10000 < ‖phi (p : K)‖*‖phi (q : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (p : K)*phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K))
      (coherentVandermonde3 (fun i => phi (a i : K)))
        (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    1 < 5*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2/
          ‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖ +
      3*‖phi (a 2 : K)‖*‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖/
        (4*‖phi (a 0 : K)‖*‖phi (p : K)‖^3) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hA1 : 1 ≤ ‖f (a 0)‖ := one_le_norm_integer hK phi (hTup.1 _ (ha 0))
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
  have hupper := (coherent_three_separated_bounds (fun i => f (a i))
    (f p) (f q) eta (hf.comp hinj) (by linarith only [hA1]) hAB hBS
    hP hAP hQ hPQ heta).1
  exact hlower.trans_lt hupper



end D1Bound5
end
