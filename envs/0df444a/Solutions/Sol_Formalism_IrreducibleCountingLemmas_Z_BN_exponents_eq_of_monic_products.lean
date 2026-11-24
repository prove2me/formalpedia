-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.exponents_eq_of_monic_products
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:00:50.952906+00:00
-- url     : https://prove2.me/submissions/cded8ee0-2ea2-4160-9e5e-edd00e81c41d

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cast_eq_of_prod_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {K Γ ι : Type} [Field K] (t : Finset ι) (f : ι → Γ → K[X])
    (hm : ∀ i ∈ t, ∀ g, (f i g).Monic)
    (hli : ∀ c : ι → K, (∀ g, ∑ i ∈ t, c i * (f i g).nextCoeff = 0) → ∀ i ∈ t, c i = 0) :
    ∀ (N : ℕ) (a b : ι → ℕ), ∑ i ∈ t, (a i + b i) ≤ N →
      (∀ g, ∏ i ∈ t, f i g ^ a i = ∏ i ∈ t, f i g ^ b i) → ∀ i ∈ t, a i = b i := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  cases hp with
  | zero =>
    intro N a b _ h i hi
    exact Nat.cast_injective (R := K) (cast_eq_of_prod_eq t f hm hli a b h i hi)
  | prime hprime =>
    have : Fact p.Prime := ⟨hprime⟩
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro a b hN h
    have hc := cast_eq_of_prod_eq t f hm hli a b h
    have hmod : ∀ i ∈ t, a i ≡ b i [MOD p] := fun i hi =>
      (CharP.natCast_eq_natCast K p).mp (hc i hi)
    obtain ⟨c, hcdef⟩ : ∃ c : ι → ℕ, c = fun i => min (a i) (b i) := ⟨_, rfl⟩
    obtain ⟨a', ha'def⟩ : ∃ a' : ι → ℕ, a' = fun i => (a i - c i) / p := ⟨_, rfl⟩
    obtain ⟨b', hb'def⟩ : ∃ b' : ι → ℕ, b' = fun i => (b i - c i) / p := ⟨_, rfl⟩
    have ha : ∀ i ∈ t, a i = c i + p * a' i := by
      intro i hi
      have hd : p ∣ a i - c i := by
        rcases le_total (a i) (b i) with hle | hle
        · simp [hcdef, hle]
        · have : c i = b i := by simp [hcdef, hle]
          rw [this]
          exact (Nat.modEq_iff_dvd' hle).mp (hmod i hi).symm
      have hle : c i ≤ a i := by simp [hcdef]
      rw [ha'def]
      simp only
      rw [Nat.mul_div_cancel' hd]
      omega
    have hb : ∀ i ∈ t, b i = c i + p * b' i := by
      intro i hi
      have hd : p ∣ b i - c i := by
        rcases le_total (b i) (a i) with hle | hle
        · simp [hcdef, hle]
        · have : c i = a i := by simp [hcdef, hle]
          rw [this]
          exact (Nat.modEq_iff_dvd' hle).mp (hmod i hi)
      have hle : c i ≤ b i := by simp [hcdef]
      rw [hb'def]
      simp only
      rw [Nat.mul_div_cancel' hd]
      omega
    have hsplit : ∀ (e e' : ι → ℕ), (∀ i ∈ t, e i = c i + p * e' i) → ∀ g,
        ∏ i ∈ t, f i g ^ e i = (∏ i ∈ t, f i g ^ c i) * (∏ i ∈ t, f i g ^ e' i) ^ p := by
      intro e e' he g
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [he i hi, pow_add, ← pow_mul, mul_comm p]
    have h' : ∀ g, ∏ i ∈ t, f i g ^ a' i = ∏ i ∈ t, f i g ^ b' i := by
      intro g
      have h2 := h g
      rw [hsplit a a' ha g, hsplit b b' hb g] at h2
      have hne : (∏ i ∈ t, f i g ^ c i) ≠ 0 :=
        (monic_prod_of_monic _ _ fun i hi => (hm i hi g).pow _).ne_zero
      have h3 := mul_left_cancel₀ hne h2
      exact frobenius_inj K[X] p h3
    have h2p : 2 ≤ p := hprime.two_le
    have hsum : 2 * ∑ i ∈ t, (a' i + b' i) ≤ ∑ i ∈ t, (a i + b i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [ha i hi, hb i hi]
      have h1 : 2 * a' i ≤ p * a' i := Nat.mul_le_mul_right _ h2p
      have h2 : 2 * b' i ≤ p * b' i := Nat.mul_le_mul_right _ h2p
      omega
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · intro i hi
      have hz : ∑ i ∈ t, (a i + b i) = 0 := by omega
      have := (Finset.sum_eq_zero_iff.mp hz) i hi
      omega
    · have hlt : ∑ i ∈ t, (a' i + b' i) < N := by omega
      have hab := ih _ hlt a' b' le_rfl h'
      intro i hi
      rw [ha i hi, hb i hi, hab i hi]
end Formalism.IrreducibleCountingLemmas.Z.BN
