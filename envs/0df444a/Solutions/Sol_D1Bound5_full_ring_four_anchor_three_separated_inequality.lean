-- Prove2me | solution 1 for D1Bound5.full_ring_four_anchor_three_separated_inequality
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:28:41.103711+00:00
-- url     : https://prove2.me/submissions/6ee73ab9-299a-439b-a28c-c6a99cdf56de

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
import Definitions.Def_D1Bound5_CoherentThreeNonvanishing_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_coherent_three_quotient_forms_not_both_zero
import Theorems.Thm_D1Bound5_full_ring_three_separated_norm_inequality
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- Four actual anchors select a nonzero integral three-anchor form.
Both alternatives use the same analytic terminal root, and the smaller
third anchor is bounded by the fourth. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup) {p q : 𝓞 K}
    (hp : p ∈ Tup) (hq : q ∈ Tup) (hpq : p ≠ q)
    (a : Fin 4 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ Tup) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hP : 1000 ≤ ‖phi (p : K)‖)
    (hTP : 4*‖phi (a 3 : K)‖ ≤ ‖phi (p : K)‖)
    (hQ : 4*‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hsize : 32*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖/
      ‖phi (a 0 : K)‖^3 ≤ ‖phi (p : K)‖^2)
    (eta : ℂ) (heta : eta^2 = phi (p : K)*phi (q : K)) :
    1 < 5*‖phi (a 1 : K)‖*‖phi (a 3 : K)‖^2/
          ‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖ +
      3*‖phi (a 3 : K)‖*‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖/
        (4*‖phi (a 0 : K)‖*‖phi (p : K)‖^3) := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  change 1000 ≤ ‖f p‖ at hP
  change 4*‖f (a 3)‖ ≤ ‖f p‖ at hTP
  change 4*‖f p‖ ≤ ‖f q‖ at hQ
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hA1 : 1 ≤ ‖f (a 0)‖ := one_le_norm_integer hK phi (hTup.1 _ (ha 0))
  have hP0 : 0 < ‖f p‖ := by linarith only [hP]
  have hAP : 1000 ≤ ‖f (a 0)‖*‖f p‖ := by
    have hh := mul_le_mul_of_nonneg_right hA1 hP0.le
    nlinarith only [hh,hP]
  have hPQ : 10000 < ‖f p‖*‖f q‖ := by
    have hh := mul_le_mul_of_nonneg_left hQ hP0.le
    nlinarith only [hh,hP,sq_nonneg (‖f p‖-1000)]
  have hn := coherent_three_quotient_forms_not_both_zero (fun i => f (a i))
    (hf.comp hinj) (f p) (f q) eta heta hA1
    (hmon (by decide)) (hmon (by decide)) (hmon (by decide))
    (by have hh := norm_nonneg (f (a 3)); linarith only [hTP,hh])
    (by linarith only [hQ,hP0]) hsize
  let b : Fin 3 → 𝓞 K := coherentTriple012 a
  let c : Fin 3 → 𝓞 K := coherentTriple013 a
  have hb : Function.Injective b :=
    hinj.comp (by decide : Function.Injective (![0,1,2] : Fin 3 → Fin 4))
  have hc : Function.Injective c :=
    hinj.comp (by decide : Function.Injective (![0,1,3] : Fin 3 → Fin 4))
  rcases hn with hn | hn
  · have hout := full_ring_three_separated_norm_inequality hK phi hTup hp hq hpq
      b hb (fun i => ha _) (fun i => hap _) (fun i => haq _)
      (hmon (by decide : (0 : Fin 4) ≤ 1)) (hmon (by decide : (1 : Fin 4) ≤ 2))
      hP0 hAP hQ hPQ eta heta hn
    apply hout.trans_le
    dsimp [b,coherentTriple012]
    gcongr <;> exact hmon (by decide : (2 : Fin 4) ≤ 3)
  · exact full_ring_three_separated_norm_inequality hK phi hTup hp hq hpq
      c hc (fun i => ha _) (fun i => hap _) (fun i => haq _)
      (hmon (by decide : (0 : Fin 4) ≤ 1)) (hmon (by decide : (1 : Fin 4) ≤ 3))
      hP0 hAP hQ hPQ eta heta hn

end D1Bound5
end
