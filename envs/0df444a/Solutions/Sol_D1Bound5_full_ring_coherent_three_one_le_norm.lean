-- Prove2me | solution 1 for D1Bound5.full_ring_coherent_three_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:29.022747+00:00
-- url     : https://prove2.me/submissions/517a8045-1cf1-4356-8f99-15d96eb456e2

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
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_IsD1
import Theorems.Thm_D1Bound5_coherentWeights3_eq_quotient
import Theorems.Thm_D1Bound5_full_ring_coherent_quotient_form_one_le_norm

section
open Finset

namespace D1Bound5





















theorem map_coherentWeights3
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Fin 3 → R) (i : Fin 3) :
    f (coherentWeights3 a i) = coherentWeights3 (fun j => f (a j)) i := by
  fin_cases i <;> simp [coherentWeights3]





theorem map_coherentWeights3_eq_quotient
    {R F : Type*} [CommRing R] [Field F]
    (f : R →+* F) (a : Fin 3 → R)
    (hinj : Function.Injective (fun i => f (a i))) (i : Fin 3) :
    f (coherentWeights3 a i) = f (coherentVandermonde3 a) * (f (a i)) ^ (3 - 2) /
      (∏ j ∈ Finset.univ.erase i, (f (a i) - f (a j))) := by
  rw [map_coherentWeights3]
  simpa only [coherentVandermonde3, map_sub, map_mul] using
    coherentWeights3_eq_quotient (fun j => f (a j)) hinj i



end D1Bound5
end

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5







/-- The true three-anchor coherent form has the full-ring lower bound. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {p q : 𝓞 K}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    (a : Fin 3 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ T) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K))
      (phi ((coherentVandermonde3 a : 𝓞 K) : K)) (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    1 ≤ ‖coherentQuotientForm (fun i => phi (a i : K))
      (phi ((coherentVandermonde3 a : 𝓞 K) : K)) (phi (p : K)) (phi (q : K)) eta‖ := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  exact full_ring_coherent_quotient_form_one_le_norm hK phi hT hp hq hpq
    a (coherentWeights3 a) (coherentVandermonde3 a) ha hap haq
    (fun i => map_coherentWeights3_eq_quotient f a (hf.comp hinj) i) eta heta hL



end D1Bound5
end
