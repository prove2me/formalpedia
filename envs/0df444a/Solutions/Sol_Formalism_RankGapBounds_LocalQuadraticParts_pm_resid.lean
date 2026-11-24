-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.pm_resid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:59.007968+00:00
-- url     : https://prove2.me/submissions/417c97b5-742c-442d-a2a5-91a7f0511590

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.RankGapBounds.LocalQuadraticParts
open Finset
private theorem natCast_zmod_eq_zero_of_dvd {M a : ℕ} (h : M ∣ a) : (a : ZMod M) = 0 := by
  exact (CharP.cast_eq_zero_iff (ZMod M) M a).mpr h
private theorem natCast_zmod_four_eq_one_or_neg_one_of_odd (l k : ℕ) (hk : k = 2) (hodd : l % 2 = 1) :
    (l : ZMod (2 ^ k)) = 1 ∨ (l : ZMod (2 ^ k)) = -1 := by
  subst hk
  rcases (show l % 4 = 1 ∨ l % 4 = 3 by omega) with h | h
  · left
    have hd : 2 ^ 2 ∣ l - 1 := by show 4 ∣ l - 1; omega
    have h0 := natCast_zmod_eq_zero_of_dvd hd
    rw [Nat.cast_sub (by omega), Nat.cast_one, sub_eq_zero] at h0
    exact h0
  · right
    have hd : 2 ^ 2 ∣ l + 1 := by show 4 ∣ l + 1; omega
    have h0 := natCast_zmod_eq_zero_of_dvd hd
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
end Formalism.RankGapBounds.LocalQuadraticParts
end

set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
open Finset
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (hI : OrdersIff) (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) (hodd : l % 2 = 1)
    (hord : orderOf (hOf e l hl) ≤ J) :
    (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = 1 ∨
      (l : ZMod (2 ^ (e + 2 - min e (Nat.log 2 J)))) = -1 := by
  have h4 := natCast_zmod_four_eq_one_or_neg_one_of_odd l (e + 2 - e) (by omega) hodd
  have hpow : (hOf e l hl) ^ (2 ^ e) = 1 := (hI e e l hl le_rfl).mpr h4
  have hdvd : orderOf (hOf e l hl) ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hiJ : 2 ^ i ≤ J := by rw [← hoi]; exact hord
  have hJ0 : J ≠ 0 := by
    have : 0 < 2 ^ i := by positivity
    omega
  have hilog : i ≤ Nat.log 2 J := by
    exact Nat.le_log_of_pow_le (by norm_num) hiJ
  have hij : i ≤ min e (Nat.log 2 J) := le_min hi hilog
  apply (hI e (min e (Nat.log 2 J)) l hl (min_le_left _ _)).mp
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [hoi]
  exact pow_dvd_pow 2 hij
end Formalism.RankGapBounds.LocalQuadraticParts
