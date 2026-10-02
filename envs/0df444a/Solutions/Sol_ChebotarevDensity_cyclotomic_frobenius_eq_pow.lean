-- Prove2me | solution 1 for ChebotarevDensity.cyclotomic_frobenius_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T13:34:34.365299+00:00
-- url     : https://prove2.me/submissions/ed8d4e06-6118-418c-8862-97a2655650fa

import Definitions.Def_ChebotarevDensity_Defs

open Polynomial NumberField
open ChebotarevDensity

private lemma under_eq_span {K : Type*} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (Q : Ideal (𝓞 K)) [Q.IsPrime] (hpQ : (p : 𝓞 K) ∈ Q) :
    Q.under ℤ = Ideal.span {(p : ℤ)} := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    exact PrincipalIdealRing.isMaximal_of_irreducible this.irreducible
  have hle : Ideal.span {(p : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa [Ideal.under] using hpQ
  exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm

theorem solution (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (σ : GalGroup (X ^ m - 1)) (hσ : IsFrobeniusAt (X ^ m - 1) p σ)
    (ζ : SplitField (X ^ m - 1)) (hζ : IsPrimitiveRoot ζ m) :
    σ ζ = ζ ^ p := by
  obtain ⟨Q, hQ, hpQ, hF⟩ := hσ
  have hunder := under_eq_span p hp Q hpQ
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
    rw [hunder]
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv]
    exact Nat.card_zmod p
  have hmQ : (m : 𝓞 (SplitField (X ^ m - 1))) ∉ Q := by
    intro h
    have : (m : ℤ) ∈ Q.under ℤ := by simpa [Ideal.under] using h
    rw [hunder, Ideal.mem_span_singleton] at this
    exact hpm (by exact_mod_cast this)
  have hint : IsIntegral ℤ ζ := by
    refine ⟨X ^ m - 1, monic_X_pow_sub_C 1 hm.ne', ?_⟩
    simp [hζ.pow_eq_one]
  let z : 𝓞 (SplitField (X ^ m - 1)) := ⟨ζ, hint⟩
  have hz : z ^ m = 1 := by
    apply Subtype.ext
    exact hζ.pow_eq_one
  have key := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hz hmQ
  rw [hcard] at key
  have := congrArg (fun x : 𝓞 (SplitField (X ^ m - 1)) => (x : SplitField (X ^ m - 1))) key
  have h2 : ((MulSemiringAction.toAlgHom ℤ (𝓞 (SplitField (X ^ m - 1))) σ z :
      𝓞 (SplitField (X ^ m - 1))) : SplitField (X ^ m - 1)) = σ ζ := rfl
  rw [h2] at this
  exact this
