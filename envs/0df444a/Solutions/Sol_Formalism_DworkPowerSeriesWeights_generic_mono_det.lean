-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.generic_mono_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:37.149006+00:00
-- url     : https://prove2.me/submissions/bbc5405c-e52f-4170-8c83-ee2ee821a195

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {R : Type*} [CommRing R] [Nontrivial R] {d N0 n : ℕ} (z : Fin N0)
    (t : Fin n → ZMod d) (L : Fin n → ℕ) (γ : Fin n → Fin N0) (hγ : Function.Injective γ)
    (hL : ∀ i, L i ≠ 0) (hinj : Function.Injective fun i => (t i, L i)) :
    (Matrix.of fun (r c : Fin n) =>
      (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)).det ≠ 0 := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      (∏ i, (Matrix.of fun (r c : Fin n) =>
        (MvPolynomial.X (t r, z, γ c) : MvPolynomial (ZMod d × Fin N0 × Fin N0) R) ^ (L r)) (σ i) i)
        = MvPolynomial.monomial (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) 1 := by
    intro σ
    rw [MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [MvPolynomial.X_pow_eq_monomial]
  have hval : ∀ (f : Fin n → ZMod d) (g : Fin n → ℕ) (i : Fin n),
      (∑ j, Finsupp.single (f j, z, γ j) (g j)) (f i, z, γ i) = g i := by
    intro f g i
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have hval2 : ∀ (i : Fin n) (u : ZMod d),
      (∑ j, Finsupp.single (t j, z, γ j) (L j)) (u, z, γ i) = if t i = u then L i else 0 := by
    intro i u
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · rw [Finsupp.single_apply]
      by_cases h : t i = u
      · simp [h]
      · rw [if_neg, if_neg h]
        intro h'
        exact h (Prod.ext_iff.mp h').1
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (hγ (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2)
    · simp
  have key : ∀ σ : Equiv.Perm (Fin n),
      (∑ i, Finsupp.single (t (σ i), z, γ i) (L (σ i))) = ∑ i, Finsupp.single (t i, z, γ i) (L i) → σ = 1 := by
    intro σ h
    ext i
    have h1 : (∑ j, Finsupp.single (t (σ j), z, γ j) (L (σ j))) (t (σ i), z, γ i)
        = (∑ j, Finsupp.single (t j, z, γ j) (L j)) (t (σ i), z, γ i) := by rw [h]
    rw [hval (fun j => t (σ j)) (fun j => L (σ j)) i, hval2] at h1
    by_cases ht : t i = t (σ i)
    · rw [if_pos ht] at h1
      have : σ i = i := hinj (Prod.ext ht.symm h1)
      simp [this]
    · rw [if_neg ht] at h1
      exact absurd h1 (hL (σ i))
  intro hdet
  have hc := congrArg (MvPolynomial.coeff (∑ i, Finsupp.single (t i, z, γ i) (L i))) hdet
  rw [Matrix.det_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))] at hc
  · rw [hprod] at hc
    simp at hc
  · intro σ _ hσ
    rw [hprod, Units.smul_def, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_neg]
    · simp
    · exact fun h => hσ (key σ h)
  · simp
end Formalism.DworkPowerSeriesWeights
