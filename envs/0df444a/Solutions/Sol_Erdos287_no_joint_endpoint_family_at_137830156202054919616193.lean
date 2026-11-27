-- Prove2me | solution 1 for Erdos287.no_joint_endpoint_family_at_137830156202054919616193
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T01:18:03.442055+00:00
-- url     : https://prove2.me/submissions/09fc9529-a752-47fb-9112-802d2664185c

import Mathlib
import Theorems.Thm_Erdos287_no_joint_endpoint_family_in_five_prime_classes
import Theorems.Thm_Erdos287_pocklington_prime_certificate

open Finset

set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

private abbrev layerPrime : ℕ := 137830156202054919616193
private abbrev certificateFactor : ℕ := 153570719213

private theorem certificateFactorPrime : Nat.Prime certificateFactor := by
  refine Erdos287.pocklington_prime_certificate certificateFactor 2599193
    (by decide) (by decide) (by decide) (by decide) ?_
  intro d hd hdiv
  have he : d = 2599193 := (Nat.prime_dvd_prime_iff_eq hd (by norm_num)).mp hdiv
  subst d
  refine ⟨2, ?_, ?_⟩
  · change ((2 : ℕ) : ZMod 153570719213) ^ 153570719212 = 1
    reduce_mod_char
  · have hpow : ((2 : ℕ) : ZMod certificateFactor) ^ ((certificateFactor - 1) / 2599193) =
        ((122234060591 : ℕ) : ZMod certificateFactor) := by
      change ((2 : ℕ) : ZMod 153570719213) ^ 59084 = ((122234060591 : ℕ) : ZMod 153570719213)
      reduce_mod_char
    rw [hpow, ← Nat.cast_one, ← Nat.cast_sub (by decide : 1 ≤ 122234060591)]
    exact (ZMod.isUnit_iff_coprime _ _).mpr (by decide : Nat.Coprime 122234060590 certificateFactor)

private theorem layerPrimeIsPrime : Nat.Prime layerPrime := by
  refine Erdos287.pocklington_prime_certificate layerPrime (29 * certificateFactor)
    (by decide) (by decide) (by decide) (by decide) ?_
  have hfull : ((2 : ℕ) : ZMod layerPrime) ^ (layerPrime - 1) = 1 := by
    change ((2 : ℕ) : ZMod 137830156202054919616193) ^ 137830156202054919616192 = 1
    reduce_mod_char
  intro d hd hdiv
  rcases hd.dvd_mul.mp hdiv with h29 | hfactor
  · have he : d = 29 := (Nat.prime_dvd_prime_iff_eq hd (by decide)).mp h29
    subst d
    refine ⟨2, hfull, ?_⟩
    have hpow : ((2 : ℕ) : ZMod layerPrime) ^ ((layerPrime - 1) / 29) =
        ((72032692126364273148386 : ℕ) : ZMod layerPrime) := by
      unfold layerPrime
      reduce_mod_char
    rw [hpow, ← Nat.cast_one, ← Nat.cast_sub (by decide : 1 ≤ 72032692126364273148386)]
    exact (ZMod.isUnit_iff_coprime _ _).mpr
      (by decide : Nat.Coprime 72032692126364273148385 layerPrime)
  · have he : d = certificateFactor :=
      (Nat.prime_dvd_prime_iff_eq hd certificateFactorPrime).mp hfactor
    subst d
    refine ⟨2, hfull, ?_⟩
    have hpow : ((2 : ℕ) : ZMod layerPrime) ^ ((layerPrime - 1) / certificateFactor) =
        ((88418591947816841816305 : ℕ) : ZMod layerPrime) := by
      unfold layerPrime certificateFactor
      reduce_mod_char
    rw [hpow, ← Nat.cast_one, ← Nat.cast_sub (by decide : 1 ≤ 88418591947816841816305)]
    exact (ZMod.isUnit_iff_coprime _ _).mpr
      (by decide : Nat.Coprime 88418591947816841816304 layerPrime)

/-- The joint trim excludes this pair of endpoints at every positive
exponent. It uses 1/20 + 1/55 = 1/22 + 1/44. -/
theorem solution (D : Finset ℕ) (e : ℕ) (he : 1 ≤ e) :
    let t := 137830156202054919616193 ^ e
    let m := 20 * t
    let M := 55 * t
    m ∈ D → M ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) → False := by
  exact Erdos287.no_joint_endpoint_family_in_five_prime_classes D layerPrime e
    layerPrimeIsPrime he (by decide) (by decide)

