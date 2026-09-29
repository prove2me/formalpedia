-- Prove2me | solution 1 for BlockCycleRotation.card_dvd_filter_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:25:19.584988+00:00
-- url     : https://prove2.me/submissions/768c60ed-3baa-45fb-8724-b7cfc80cf61a

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_card_mod_filter_le
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The divisibility condition confines `b'` to one residue class.** -/
theorem solution {m a a' U : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1)
    (hU : ∀ b ∈ Finset.Ico 1 U, a' * b ≤ m) :
    (((Finset.Ico 1 U).filter (fun b => a ∣ (m - a' * b))).card) ≤ U / a + 1:= by
  classical
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Ico 1 U).filter (fun b => a ∣ (m - a' * b))) with he | ⟨b₀, hb₀⟩
  · rw [he]
    simp
  · refine le_trans (Finset.card_le_card ?_) (card_mod_filter_le (c := b₀ % a) ha)
    intro b hb
    simp only [Finset.mem_filter] at hb hb₀ ⊢
    refine ⟨hb.1, ?_⟩
    -- `a ∣ a' * (b₀ - b)` over `ℤ`, and `gcd a a' = 1`, so `b ≡ b₀ mod a`
    have hle : a' * b ≤ m := hU b hb.1
    have hle₀ : a' * b₀ ≤ m := hU b₀ hb₀.1
    have hz : ((a : ℤ)) ∣ ((a' : ℤ) * ((b₀ : ℤ) - (b : ℤ))) := by
      have h1 : ((a : ℤ)) ∣ ((m : ℤ) - (a' : ℤ) * (b : ℤ)) := by
        have := Int.natCast_dvd_natCast.2 hb.2
        rwa [Nat.cast_sub hle, Nat.cast_mul] at this
      have h2 : ((a : ℤ)) ∣ ((m : ℤ) - (a' : ℤ) * (b₀ : ℤ)) := by
        have := Int.natCast_dvd_natCast.2 hb₀.2
        rwa [Nat.cast_sub hle₀, Nat.cast_mul] at this
      have := dvd_sub h1 h2
      have heq : ((m : ℤ) - (a' : ℤ) * (b : ℤ)) - ((m : ℤ) - (a' : ℤ) * (b₀ : ℤ))
          = (a' : ℤ) * ((b₀ : ℤ) - (b : ℤ)) := by ring
      rwa [heq] at this
    have hco : IsCoprime (a : ℤ) (a' : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa using hgcd
    have hdvd : ((a : ℤ)) ∣ ((b₀ : ℤ) - (b : ℤ)) := IsCoprime.dvd_of_dvd_mul_left hco hz
    have : b ≡ b₀ [MOD a] := (Nat.modEq_iff_dvd).2 hdvd
    exact this
