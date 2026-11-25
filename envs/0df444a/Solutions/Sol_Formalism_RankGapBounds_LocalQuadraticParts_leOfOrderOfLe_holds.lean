-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.leOfOrderOfLe_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:08.008436+00:00
-- url     : https://prove2.me/submissions/592dcd73-60f2-4aff-b837-bec91fd47b41

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_nat_eq_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_nat_eq_neg_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_odd_of_coprime
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_powTwoPowEqOneIff_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution : OrdersBound := by
  intro e J l hl hJ hl1 hord
  have hodd := odd_of_coprime e l hl
  have hE : (hOf e l hl) ^ (2 ^ e) = 1 := by
    rw [powTwoPowEqOneIff_holds e e l hl le_rfl, show e + 2 - e = 2 by omega, zmod_nat_eq_one_iff,
      zmod_nat_eq_neg_one_iff]
    obtain ⟨k, hk⟩ := hodd
    push_cast
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      rw [hk, hb]
      exact ⟨b, by ring⟩
    · right
      rw [hk, hb]
      exact ⟨b + 1, by ring⟩
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hE)
  have hk1 : (hOf e l hl) ^ (2 ^ k) = 1 := by
    rw [← hko]
    exact pow_orderOf_eq_one _
  have hres := (powTwoPowEqOneIff_holds e k l hl hk).mp hk1
  rw [zmod_nat_eq_one_iff, zmod_nat_eq_neg_one_iff] at hres
  have hM : ((2 : ℤ) ^ (e + 2 - k)) ≤ (l : ℤ) + 1 := by
    rcases hres with h | h
    · push_cast at h
      have hpos : (0 : ℤ) < l - 1 := by omega
      have := Int.le_of_dvd hpos h
      linarith
    · push_cast at h
      have hpos : (0 : ℤ) < l + 1 := by omega
      have := Int.le_of_dvd hpos h
      linarith
  have hJn : 2 ^ k ≤ J := hko ▸ hord
  have hJ' : (2 : ℝ) ^ k ≤ J := by exact_mod_cast hJn
  have key : (4 * 2 ^ e : ℝ) = 2 ^ (e + 2 - k) * 2 ^ k := by
    rw [← pow_add, show e + 2 - k + k = e + 2 by omega]
    ring
  have h1 : (4 * 2 ^ e : ℝ) / J ≤ 4 * 2 ^ e / 2 ^ k :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hJ'
  have h2 : (4 * 2 ^ e : ℝ) / 2 ^ k = 2 ^ (e + 2 - k) := by
    rw [key]
    field_simp
  have h3 : (2 : ℝ) ^ (e + 2 - k) ≤ l + 1 := by exact_mod_cast hM
  linarith
end Formalism.RankGapBounds.LocalQuadraticParts
