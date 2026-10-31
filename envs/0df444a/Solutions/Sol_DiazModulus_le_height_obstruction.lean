-- Prove2me | solution 1 for DiazModulus.le_height_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:01:06.610135+00:00
-- url     : https://prove2.me/submissions/df29e4e3-adfe-4c40-a563-fb33e460687a

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_exists_le_translate_of_le_torusVanishing
import Theorems.Thm_DiazModulus_ringKrullDim_quotient_sectionIdeal_le
import Theorems.Thm_DiazModulus_card_le_height_add_of_ringKrullDim_quotient_le
import Theorems.Thm_DiazModulus_torusTransl_algEquiv

open Complex ComplexConjugate

/-! # The height bound (H\*) for primes over the obstruction ideal

Let `p` be a prime containing `A = J₀ + span F`. By Z3 (`exists_le_translate_of_le_torusVanishing`, applied to
the section ideal `𝔞 = sectionIdeal ℓ ψ ≤ I(Stab 𝔭)`) there is `g` with `𝔞 ≤ q := p.comap σ_g`. The ring
`R ⧸ q` is a quotient of `R ⧸ 𝔞`, so `dim R ⧸ q ≤ dim R ⧸ 𝔞 ≤ |H| + |J|` (`ringKrullDim_le_of_surjective`
and H2, `ringKrullDim_quotient_sectionIdeal_le`). The bridge H3 (`card_le_height_add_of_ringKrullDim_quotient_le`,
`ℂ` algebraically closed) gives `|A₀| + 2|A₁| = #(A₀ ⊕ A₁ × Bool) ≤ ht q + |H| + |J|`. Since `σ_g` is a ring
automorphism (V2), `ht q = ht p` (`RingEquiv.height_comap`). With `|H| ≤ |A₀|` and `|J| ≤ |A₁|` this is
`|A₁| + (d − (|H| + |J|)) ≤ ht p` in `ℕ∞` (the case `ht p = ⊤` being trivial). -/

namespace C13_Z4
open DiazModulus

/-- The arithmetic step in `ℕ∞`. -/
theorem enat_step (h : ℕ∞) (d₀ d₁ k a b : ℕ) (ha : a ≤ d₀) (hb : b ≤ d₁) (hk : k = a + b)
    (hle : ((d₀ + d₁ * 2 : ℕ) : ℕ∞) ≤ h + (k : ℕ)) : ((d₁ + ((d₀ + d₁) - k) : ℕ) : ℕ∞) ≤ h := by
  induction h using ENat.recTopCoe with
  | top => exact le_top
  | coe n =>
    have hle' : d₀ + d₁ * 2 ≤ n + k := by exact_mod_cast hle
    exact_mod_cast (by omega : d₁ + ((d₀ + d₁) - k) ≤ n)

end C13_Z4

open DiazModulus C13_Z4 in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (P : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ) (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ)))
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ r : ℕ) (𝔭 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) (h𝔭 : 𝔭.IsPrime)
    (hJ𝔭 : torusIdeal ℂ A₀ A₁ ≤ 𝔭)
    (hc : ∀ z : TorusGroup ℂ A₀ A₁, torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ 𝔭.comap (torusTransl z) →
        𝔭.comap (torusTransl z) ∈ (torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) {1} : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))).minimalPrimes)
    (H : Finset A₀) (J : Finset A₁) (ℓ : A₀ → A₀ → ℂ) (ψ : A₁ → A₁ → ℤ)
    (hℓ : ∀ h ∉ H, ℓ h h = 1 ∧ ∀ h' ∉ H, h' ≠ h → ℓ h h' = 0) (hψ : ∀ i ∉ J, ψ i i ≠ 0 ∧ ∀ i' ∉ J, i' ≠ i → ψ i i' = 0)
    (h𝔞 : sectionIdeal ℓ ψ ≤ torusVanishing (torusStab 𝔭)) :
    ∀ p : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ), p.IsPrime → torusIdeal ℂ A₀ A₁ ⊔ Ideal.span (obstructionSpan P W u a (r * M₁) (r * M₀) (torusZero 𝔭) : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ≤ p →
      ((Fintype.card A₁ + ((Fintype.card A₀ + Fintype.card A₁) - (H.card + J.card)) : ℕ) : ℕ∞) ≤ p.height := by
  intro p hp hAp
  obtain ⟨g, hg⟩ := DiazModulus.exists_le_translate_of_le_torusVanishing P W u a M₀ M₁ r 𝔭 h𝔭 hJ𝔭 hc
    (sectionIdeal ℓ ψ) h𝔞 p hp hAp
  obtain ⟨⟨e, he, -⟩, -⟩ := DiazModulus.torusTransl_algEquiv g
  have hqe : p.comap (torusTransl g) = p.comap e.toRingEquiv := by
    ext f
    simp [Ideal.mem_comap, he]
  have hq : (p.comap (torusTransl g)).IsPrime := Ideal.comap_isPrime _ _
  have hht : (p.comap (torusTransl g)).height = p.height := by
    rw [hqe]
    exact RingEquiv.height_comap _ _
  have hdim : ringKrullDim (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ ⧸ p.comap (torusTransl g)) ≤
      ((H.card + J.card : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hg)).trans
      (DiazModulus.ringKrullDim_quotient_sectionIdeal_le H J ℓ ψ hℓ hψ)
  have hb := DiazModulus.card_le_height_add_of_ringKrullDim_quotient_le _ hq (H.card + J.card) hdim
  rw [hht] at hb
  have hcard : Nat.card (A₀ ⊕ (A₁ × Bool)) = Fintype.card A₀ + Fintype.card A₁ * 2 := by
    simp [Nat.card_eq_fintype_card]
  rw [hcard] at hb
  exact enat_step _ _ _ _ _ _ (Finset.card_le_univ H) (Finset.card_le_univ J) rfl hb
