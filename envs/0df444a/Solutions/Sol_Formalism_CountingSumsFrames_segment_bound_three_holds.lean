-- Prove2me | solution 1 for Formalism.CountingSumsFrames.segment_bound_three_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:28.946617+00:00
-- url     : https://prove2.me/submissions/5d9cd57f-0ab0-4cef-8163-aa1a867c08de

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds

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
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : DigitSumValuationBound := by
  intro p _ n r a ha hn
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  have hne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1
  have hS : (p.digits n).sum ≤ n := Nat.digit_sum_le p n
  have hleg := sub_one_mul_padicValNat_factorial (p := p) n
  have hreal : ((p : ℝ) - 1) * (padicValNat p n.factorial : ℝ) = (n : ℝ) - ((p.digits n).sum : ℝ) := by
    have h1 : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) = ((n - (p.digits n).sum : ℕ) : ℝ) := by
      rw [hleg]
    rw [Nat.cast_mul, Nat.cast_sub hS, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at h1
    linarith
  have hii : (n : ℝ) / ((p : ℝ) - 1) - padicValNat p n.factorial =
      ((p.digits n).sum : ℝ) / ((p : ℝ) - 1) := by
    rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
    linarith
  have hY : (1 : ℝ) ≤ 8 * a + r := by
    have := (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    linarith
  have hp1' : (1 : ℝ) < p := by exact_mod_cast hp2
  refine ⟨?_, hii, ?_⟩
  · rw [hii]
    positivity
  · rw [hii, div_le_iff₀ hp1]
    rcases Nat.eq_zero_or_pos n with h0 | hnpos
    · subst h0
      have h00 : ((p.digits 0).sum : ℝ) = 0 := by simp
      rw [h00]
      unfold lgSeg
      exact mul_nonneg (by linarith [Real.logb_nonneg hp1' hY]) hp1.le
    · have hlen := Nat.digits_len p n hp2 (by omega)
      have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
        have := List.sum_le_card_nsmul (p.digits n) (p - 1)
          (fun x hx => by have := Nat.digits_lt_base hp2 hx; omega)
        simpa using this
      have hlog : (Nat.log p n : ℝ) ≤ Real.logb p (8 * a + r) := by
        have h1 : ((p : ℝ) ^ (Nat.log p n)) ≤ (n : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self p (by omega)
        calc (Nat.log p n : ℝ) ≤ Real.logb p n := by
              rw [Real.le_logb_iff_rpow_le hp1' (by exact_mod_cast hnpos), Real.rpow_natCast]
              exact h1
          _ ≤ Real.logb p (8 * a + r) :=
              Real.logb_le_logb_of_le hp1' (by exact_mod_cast hnpos) hn
      have hS' : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
        have h2 : ((p.digits n).sum : ℝ) ≤ (((p.digits n).length * (p - 1) : ℕ) : ℝ) := by
          exact_mod_cast hsum
        rw [hlen] at h2
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_add, Nat.cast_one] at h2
        linarith
      unfold lgSeg
      nlinarith [hlog, hp1]
end Formalism.CountingSumsFrames
