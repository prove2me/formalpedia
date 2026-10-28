-- Prove2me | solution 1 for D1Bound5.full_ring_coherent_quotient_form_one_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:24:03.774851+00:00
-- url     : https://prove2.me/submissions/1403a642-835e-43e6-bc98-55fae4a6531e

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
import Theorems.Thm_D1Bound5_full_ring_coherent_linear_form_one_le_norm

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5



/-- An explicit equality with source-ring polynomial weights transfers
the already proved integral lower bound to the manuscript quotient form. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {p q : 𝓞 K}
    (hp : p ∈ T) (hq : q ∈ T) (hpq : p ≠ q)
    {m : ℕ} (a c : Fin m → 𝓞 K) (Delta : 𝓞 K)
    (ha : ∀ i, a i ∈ T) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hc : ∀ i, phi (c i : K) =
      phi (Delta : K) * (phi (a i : K)) ^ (m - 2) /
        (∏ j ∈ Finset.univ.erase i, (phi (a i : K) - phi (a j : K))))
    (eta : ℂ) (heta : eta ^ 2 = phi (p : K) * phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K)) (phi (Delta : K))
      (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    1 ≤ ‖coherentQuotientForm (fun i => phi (a i : K)) (phi (Delta : K))
      (phi (p : K)) (phi (q : K)) eta‖ := by
  have heq : coherentQuotientForm (fun i => phi (a i : K)) (phi (Delta : K))
      (phi (p : K)) (phi (q : K)) eta =
      -phi (Delta : K) * coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta +
        ∑ i, phi (c i : K) *
          coherentAnchorRoot (phi (a i : K)) (phi (p : K)) (phi (q : K)) eta := by
    unfold coherentQuotientForm
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc i]
  rw [heq] at hL ⊢
  exact full_ring_coherent_linear_form_one_le_norm hK phi hT hp hq hpq
    a c Delta ha hap haq eta heta hL







end D1Bound5
end
