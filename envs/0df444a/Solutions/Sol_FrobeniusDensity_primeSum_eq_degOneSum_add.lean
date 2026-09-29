-- Prove2me | solution 1 for FrobeniusDensity.primeSum_eq_degOneSum_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/acef0bae-c2e1-5a4a-b91c-471aa38fd2d2

import Definitions.Def_FrobeniusDensity_PrimeSums
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add

set_option autoImplicit false

p2m_open "Ideal NumberField IsDedekindDomain Ideal.IsDedekindDomain"
open scoped ENNReal

namespace FrobeniusDensity
p2m_export "FrobeniusDensity" "normRpow primeSum degOneSum cutSum tailSum degOneCount_of_not_prime degOneCount_of_prime degOneCount ratPrimeIdeal ne_bot_of_liesOver_ratPrimeIdeal"
p2m_open "FrobeniusDensity"

variable (K : Type*) [Field K] [NumberField K]

private def PrimeNormFiber (ℓ : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // Ideal.absNorm v.asIdeal = ℓ}

private noncomputable def primeNormFiberEquiv :
    (Σ ℓ : ℕ, PrimeNormFiber K ℓ) ≃ HeightOneSpectrum (𝓞 K) where
  toFun p := p.2.1
  invFun v := ⟨Ideal.absNorm v.asIdeal, v, rfl⟩
  left_inv p := by rcases p with ⟨ℓ, v, rfl⟩; rfl
  right_inv v := rfl

private scoped instance (ℓ : ℕ) : Finite (PrimeNormFiber K ℓ) := by
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = ℓ} :=
    (Ideal.finite_setOf_absNorm_eq ℓ).to_subtype
  exact Finite.of_injective
    (fun v => (⟨v.1.asIdeal, v.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = ℓ}))
    fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))

private theorem liesOver_of_absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hv : Ideal.absNorm v.asIdeal = ℓ) : v.asIdeal.LiesOver (ratPrimeIdeal ℓ) := by
  refine ⟨?_⟩
  have := Ideal.span_singleton_absNorm (I := v.asIdeal) (by rw [hv]; exact hℓ)
  rw [hv] at this
  exact this

private theorem natCard_primeNormFiber {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Nat.card (PrimeNormFiber K ℓ) = degOneCount K ℓ := by
  rw [degOneCount_of_prime K hℓ, ← Nat.card_coe_set_eq]
  have hcard : ∀ I : Ideal (𝓞 K), Nat.card ((𝓞 K) ⧸ I) = Ideal.absNorm I := fun I =>
    (Submodule.cardQuot_apply _).symm.trans (Ideal.absNorm_apply I).symm
  refine Nat.card_congr ⟨fun v => ⟨v.1.asIdeal, ?_⟩, fun 𝔮 => ⟨⟨𝔮.1, 𝔮.2.1.1, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact ⟨⟨v.1.isPrime, liesOver_of_absNorm_eq K hℓ v.2⟩, (hcard _).trans v.2⟩
  · haveI := 𝔮.2.1.1
    haveI := 𝔮.2.1.2
    exact ne_bot_of_liesOver_ratPrimeIdeal hℓ
  · exact (hcard 𝔮.1).symm.trans 𝔮.2.2
  · intro v; rfl
  · intro 𝔮; rfl

private lemma tsum_reindex {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑' a, f (e a) = ∑' b, f b := by
  refine le_antisymm (ENNReal.tsum_comp_le_tsum_of_injective e.injective f) ?_
  simpa using ENNReal.tsum_comp_le_tsum_of_injective e.symm.injective fun a => f (e a)

private theorem tsum_degOne_eq (s : ℝ) :
    (∑' v : HeightOneSpectrum (𝓞 K),
        if (Ideal.absNorm v.asIdeal).Prime then normRpow K s v.asIdeal else 0)
      = ∑' ℓ : ℕ, (degOneCount K ℓ : ℝ≥0∞) * (ℓ : ℝ≥0∞) ^ (-s) := by
  rw [← tsum_reindex (primeNormFiberEquiv K)
    (fun v => if (Ideal.absNorm v.asIdeal).Prime then normRpow K s v.asIdeal else 0),
    ENNReal.tsum_sigma']
  refine tsum_congr fun ℓ => ?_
  have hfib : ∀ v : PrimeNormFiber K ℓ,
      (if (Ideal.absNorm (primeNormFiberEquiv K ⟨ℓ, v⟩).asIdeal).Prime
        then normRpow K s (primeNormFiberEquiv K ⟨ℓ, v⟩).asIdeal else 0)
      = (if ℓ.Prime then (ℓ : ℝ≥0∞) ^ (-s) else 0) := by
    intro v
    have hv : Ideal.absNorm (primeNormFiberEquiv K ⟨ℓ, v⟩).asIdeal = ℓ := v.2
    rw [normRpow, hv]
  rw [tsum_congr hfib, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  by_cases hℓ : ℓ.Prime
  · rw [if_pos hℓ, natCard_primeNormFiber K hℓ]
    norm_cast
  · rw [if_neg hℓ, mul_zero, degOneCount_of_not_prime K hℓ, Nat.cast_zero, zero_mul]

end FrobeniusDensity
p2m_reactivate "P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add.FrobeniusDensity"

p2m_open "FrobeniusDensity P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add.FrobeniusDensity"

theorem solution (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by
  have hsplit : primeSum K s
      = (∑' v : HeightOneSpectrum (𝓞 K),
          if (Ideal.absNorm v.asIdeal).Prime then normRpow K s v.asIdeal else 0)
        + tailSum K s := by
    rw [primeSum, tailSum, ← ENNReal.tsum_add]
    refine tsum_congr fun v => ?_
    by_cases hv : (Ideal.absNorm v.asIdeal).Prime
    · rw [if_pos hv, if_pos hv, add_zero]
    · rw [if_neg hv, if_neg hv, zero_add]
  rw [hsplit, tsum_degOne_eq, degOneSum, cutSum, ← ENNReal.tsum_add]
  congr 1
  refine tsum_congr fun ℓ => ?_
  by_cases hℓ : ℓ ∈ S₀
  · rw [if_pos hℓ, if_pos hℓ, zero_mul, zero_add]
  · rw [if_neg hℓ, if_neg hℓ, zero_mul, add_zero]

end S_FrobeniusDensity_primeSum_eq_degOneSum_add
end P2MW
export P2MW.S_FrobeniusDensity_primeSum_eq_degOneSum_add (solution)
