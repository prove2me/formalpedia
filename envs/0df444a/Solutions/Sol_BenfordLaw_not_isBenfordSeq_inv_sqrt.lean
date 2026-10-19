-- Prove2me | solution 1 for BenfordLaw.not_isBenfordSeq_inv_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:04:55.740992+00:00
-- url     : https://prove2.me/submissions/44836d3d-7af9-4a15-9de0-89848c28a522

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw

namespace BenfordNonBenford

/-- If `10^e ≤ x < 2·10^e` then the leading digit of `x` is `1`. -/
lemma ld_one (x : ℝ) (e : ℤ) (h1 : (10 : ℝ) ^ e ≤ x) (h2 : x < 2 * (10 : ℝ) ^ e) :
    leadingDigit 10 x = 1 := by
  have hpe : (0 : ℝ) < (10 : ℝ) ^ e := by positivity
  have hx : 0 < x := lt_of_lt_of_le hpe h1
  have hb : (1 : ℝ) < 10 := by norm_num
  have hz : ((10 : ℝ) ^ e) = (10 : ℝ) ^ (e : ℝ) := (Real.rpow_intCast 10 e).symm
  have hlo : (e : ℝ) ≤ Real.logb 10 x := by
    rw [Real.le_logb_iff_rpow_le hb hx, ← hz]; exact h1
  have hhi : Real.logb 10 x < e + 1 := by
    rw [Real.logb_lt_iff_lt_rpow hb hx, Real.rpow_add (by norm_num), ← hz, Real.rpow_one]
    linarith
  have hfr : Int.fract (Real.logb 10 x) = Real.logb 10 x - e := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, e, by ring⟩
  unfold leadingDigit
  rw [Nat.floor_eq_iff (by positivity)]
  push_cast
  rw [hfr, Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx, ← hz]
  constructor
  · rw [le_div_iff₀ hpe]; linarith
  · rw [div_lt_iff₀ hpe]; norm_num; linarith

lemma logb_two_lt_half : Real.logb 10 2 < 1 / 2 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.lt_sqrt (by norm_num)]
  norm_num

/-- A sequence whose digit-`1` frequency is at least `1/2` along `N = f J` (with `J ≤ f J`)
is not Benford. -/
lemma not_benford_of_freq (a : ℕ → ℝ) (f : ℕ → ℕ) (hf : ∀ J, J ≤ f J)
    (hfreq : ∀ J, 1 / 2 ≤ digitFreq 10 1 a (f J)) : ¬ IsBenfordSeq 10 a := by
  intro h
  have ht := h 1 le_rfl (by norm_num)
  have hb : benfordProb 10 1 < 1 / 2 := by
    unfold benfordProb; norm_num; exact logb_two_lt_half
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hb))
  have := hN0 (f N0) (hf N0)
  linarith [hfreq N0]

lemma freq_ge (a : ℕ → ℝ) (N lo hi : ℕ) (hhi : hi ≤ N) (hN : 0 < N)
    (hcard : (N : ℝ) ≤ 2 * ((hi - lo : ℕ) : ℝ))
    (hld : ∀ n, lo ≤ n → n < hi → leadingDigit 10 (a n) = 1) :
    1 / 2 ≤ digitFreq 10 1 a N := by
  unfold digitFreq
  have hsub : Finset.Ico lo hi ⊆ (Finset.range N).filter (fun n => leadingDigit 10 (a n) = 1) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hld n hn.1 hn.2⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr]
  have : ((hi - lo : ℕ) : ℝ) ≤ (((Finset.range N).filter
      (fun n => leadingDigit 10 (a n) = 1)).card : ℝ) := by exact_mod_cast hc
  linarith

end BenfordNonBenford

open BenfordNonBenford in
theorem solution :
    ¬ IsBenfordSeq 10 (fun n => 1 / ((n : ℝ) + 1)) ∧
      ¬ IsBenfordSeq 10 (fun n => Real.sqrt ((n : ℝ) + 1)) := by
  constructor
  · -- N = 10^(J+1); the indices 5·10^J ≤ n < 10^(J+1) give leading digit 1
    refine not_benford_of_freq _ (fun J => 10 ^ (J + 1)) (fun J => ?_) (fun J => ?_)
    · have := Nat.lt_pow_self (n := J + 1) (by norm_num : 1 < 10); omega
    · refine freq_ge _ _ (5 * 10 ^ J) (10 ^ (J + 1)) le_rfl (by positivity) ?_ ?_
      · rw [Nat.cast_sub (by rw [pow_succ]; omega)]; push_cast; rw [pow_succ]; linarith
      · intro n hlo hhi
        have hlo' : (5 : ℝ) * 10 ^ J ≤ n := by exact_mod_cast hlo
        have hhi' : (n : ℝ) + 1 ≤ 10 ^ (J + 1) := by exact_mod_cast hhi
        have hp : (0 : ℝ) < 10 ^ J := by positivity
        have hz : (10 : ℝ) ^ (-((J : ℤ) + 1)) = 1 / 10 ^ (J + 1) := by
          rw [zpow_neg, one_div]; norm_cast
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        refine ld_one _ (-((J : ℤ) + 1)) ?_ ?_
        · rw [hz]; exact one_div_le_one_div_of_le hn1 hhi'
        · rw [hz, div_lt_iff₀ hn1, show 2 * (1 / (10 : ℝ) ^ (J + 1)) * (n + 1) = 2 * (n + 1) / 10 ^ (J + 1) by ring,
            one_lt_div (by positivity), pow_succ]
          nlinarith
  · -- N = 4·100^J; the indices 100^J ≤ n < 3·100^J give leading digit 1
    refine not_benford_of_freq _ (fun J => 4 * 100 ^ J) (fun J => ?_) (fun J => ?_)
    · have := Nat.lt_pow_self (n := J) (by norm_num : 1 < 100); omega
    · refine freq_ge _ _ (100 ^ J) (3 * 100 ^ J) (by omega) (by positivity) ?_ ?_
      · rw [Nat.cast_sub (by omega)]; push_cast; linarith
      · intro n hlo hhi
        have hlo' : (100 : ℝ) ^ J ≤ n := by exact_mod_cast hlo
        have hhi' : (n : ℝ) + 1 ≤ 3 * 100 ^ J := by exact_mod_cast hhi
        have hp : (0 : ℝ) < 100 ^ J := by positivity
        have h100 : ((10 : ℝ) ^ J) ^ 2 = 100 ^ J := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        refine ld_one _ (J : ℤ) ?_ ?_
        · rw [zpow_natCast, Real.le_sqrt (by positivity) (by positivity), h100]; linarith
        · rw [zpow_natCast, Real.sqrt_lt' (by positivity), mul_pow, h100]; linarith
