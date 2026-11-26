-- Prove2me | solution 1 for Erdos266.slope_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:42:06.674293+00:00
-- url     : https://prove2.me/submissions/2f1ae338-1702-4256-aee9-9a23b1b684e2

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma
public import Theorems.Thm_Erdos266_abs_prod_sub_pow_le
public import Theorems.Thm_Erdos266_abs_prod_le
public import Theorems.Thm_Erdos266_prod_lower
public import Theorems.Thm_Erdos266_prod_shift_sub
public import Theorems.Thm_Erdos266_abs_tSeq_le


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
set_option maxHeartbeats 1600000
namespace Erdos266
theorem _root_.solution (i : ℕ) (hi : 1 ≤ i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (n : ℤ),
      4 * (i : ℝ) * |(n : ℝ)| ≤ (N : ℝ) →
      |f i (N : ℝ) - f i ((N : ℝ) + (n : ℝ)) - i * n / (N : ℝ) ^ (i + 1)|
        ≤ C * (n : ℝ) ^ 2 / (N : ℝ) ^ (i + 2) := by
  refine ⟨3 * ((i : ℝ) + 1) ^ 2 * 16 ^ i, by positivity, ?_⟩
  intro N n hNn
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  -- numeric groundwork
  have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by nlinarith) hNn
  obtain ⟨B, hBdef⟩ : ∃ b : ℝ, b = |(n : ℝ)| + i := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hB2 : B ≤ (N : ℝ) / 2 := by
    have h1 : (0 : ℝ) ≤ ((i : ℝ) - 1) * (|(n : ℝ)| - 1) :=
      mul_nonneg (by linarith) (by linarith)
    rw [hBdef]
    nlinarith
  have hBN : B ≤ (N : ℝ) := by linarith
  have ht : ∀ j ∈ range i, |(tSeq j : ℝ)| ≤ B := by
    intro j hj
    have h1 : |tSeq j| ≤ (j : ℚ) + 1 := abs_tSeq_le j
    have h2 : |(tSeq j : ℝ)| ≤ (j : ℝ) + 1 := by exact_mod_cast h1
    have h3 : (j : ℝ) + 1 ≤ i := by exact_mod_cast mem_range.mp hj
    rw [hBdef]
    linarith [abs_nonneg (n : ℝ)]
  have hnt : ∀ j ∈ range i, |(n : ℝ) + (tSeq j : ℝ)| ≤ B := by
    intro j hj
    refine (abs_add_le _ _).trans ?_
    have h1 := ht j hj
    rw [hBdef] at h1 ⊢
    have h3 : (j : ℝ) + 1 ≤ i := by exact_mod_cast mem_range.mp hj
    have h2 : |(tSeq j : ℝ)| ≤ (j : ℝ) + 1 := by
      exact_mod_cast abs_tSeq_le j
    linarith
  -- the two products
  obtain ⟨P, hPdef⟩ : ∃ p : ℝ, p = ∏ j ∈ range i, ((N : ℝ) + (tSeq j : ℝ)) := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ q : ℝ, q = ∏ j ∈ range i, ((N : ℝ) + ((n : ℝ) + (tSeq j : ℝ))) :=
    ⟨_, rfl⟩
  have hfP : f i (N : ℝ) = P⁻¹ := by rw [hPdef]; rfl
  have hfQ : f i ((N : ℝ) + (n : ℝ)) = Q⁻¹ := by
    rw [hQdef, f]
    congr 1
    exact prod_congr rfl fun j _ => by ring
  have hPlow : ((N : ℝ) / 2) ^ i ≤ P := by
    have := prod_lower (s := range i) hB0 hB2 ht
    rwa [card_range, ← hPdef] at this
  have hQlow : ((N : ℝ) / 2) ^ i ≤ Q := by
    have := prod_lower (s := range i) hB0 hB2 hnt
    rwa [card_range, ← hQdef] at this
  have hPpos : 0 < P := lt_of_lt_of_le (by positivity) hPlow
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity) hQlow
  have hPsub : |P - (N : ℝ) ^ i| ≤ 2 ^ i * B * (N : ℝ) ^ i / N := by
    have := abs_prod_sub_pow_le (s := range i) hB0 hBN hNpos ht
    rw [card_range, ← hPdef] at this
    refine this.trans ?_
    gcongr
    linarith [pow_pos (show (0:ℝ) < 2 by norm_num) i]
  have hQsub : |Q - (N : ℝ) ^ i| ≤ 2 ^ i * B * (N : ℝ) ^ i / N := by
    have := abs_prod_sub_pow_le (s := range i) hB0 hBN hNpos hnt
    rw [card_range, ← hQdef] at this
    refine this.trans ?_
    gcongr
    linarith [pow_pos (show (0:ℝ) < 2 by norm_num) i]
  have hQabs : |Q| ≤ 2 ^ i * (N : ℝ) ^ i := by
    have := abs_prod_le (s := range i) hB0 hBN hnt
    rwa [card_range, mul_pow, ← hQdef] at this
  -- telescoping and the sum of hybrid products
  obtain ⟨S, hSdef⟩ : ∃ s : ℝ, s = ∑ k ∈ range i, ∏ j ∈ (range i).erase k,
      ((N : ℝ) + if j < k then (n : ℝ) + (tSeq j : ℝ) else (tSeq j : ℝ)) := ⟨_, rfl⟩
  have htel : Q - P = (n : ℝ) * S := by
    rw [hPdef, hQdef, hSdef]
    exact prod_shift_sub i (N : ℝ) (n : ℝ)
  have hG : ∀ k ∈ range i, |(∏ j ∈ (range i).erase k,
      ((N : ℝ) + if j < k then (n : ℝ) + (tSeq j : ℝ) else (tSeq j : ℝ)))
        - (N : ℝ) ^ i / N| ≤ 2 ^ i * B * ((N : ℝ) ^ i / N) / N := by
    intro k hk
    have hcb : ∀ j ∈ (range i).erase k,
        |if j < k then (n : ℝ) + (tSeq j : ℝ) else (tSeq j : ℝ)| ≤ B := by
      intro j hj
      split_ifs
      · exact hnt j (mem_of_mem_erase hj)
      · exact ht j (mem_of_mem_erase hj)
    have := abs_prod_sub_pow_le (s := (range i).erase k)
      (c := fun j => if j < k then (n : ℝ) + (tSeq j : ℝ) else (tSeq j : ℝ))
      hB0 hBN hNpos hcb
    rw [card_erase_of_mem hk, card_range] at this
    have hpow : (N : ℝ) ^ (i - 1) = (N : ℝ) ^ i / N := by
      rw [eq_div_iff hNpos.ne', ← pow_succ]
      congr 1
      omega
    rw [hpow] at this
    refine this.trans ?_
    have h2 : (2:ℝ) ^ (i - 1) ≤ 2 ^ i :=
      pow_le_pow_right₀ one_le_two (Nat.sub_le i 1)
    gcongr
    linarith [pow_pos (show (0:ℝ) < 2 by norm_num) (i - 1)]
  have hS : |S - i * ((N : ℝ) ^ i / N)| ≤ i * (2 ^ i * B * ((N : ℝ) ^ i / N) / N) := by
    have hrw : S - i * ((N : ℝ) ^ i / N)
        = ∑ k ∈ range i, ((∏ j ∈ (range i).erase k,
            ((N : ℝ) + if j < k then (n : ℝ) + (tSeq j : ℝ) else (tSeq j : ℝ)))
              - (N : ℝ) ^ i / N) := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, hSdef]
    rw [hrw]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range i, |(∏ j ∈ (range i).erase k,
          ((N : ℝ) + if j < k then (n : ℝ) + (tSeq j : ℝ) else (tSeq j : ℝ)))
            - (N : ℝ) ^ i / N|
        ≤ ∑ _k ∈ range i, 2 ^ i * B * ((N : ℝ) ^ i / N) / N := sum_le_sum hG
    _ = i * (2 ^ i * B * ((N : ℝ) ^ i / N) / N) := by
        rw [sum_const, card_range, nsmul_eq_mul]
  -- the split into two error terms
  have h2i : (N : ℝ) ^ (2 * i) = (N : ℝ) ^ i * (N : ℝ) ^ i := by
    rw [← pow_add]
    congr 1
    omega
  have hPQlow : (N : ℝ) ^ (2 * i) / 4 ^ i ≤ P * Q := by
    have h1 : ((N : ℝ) / 2) ^ i * ((N : ℝ) / 2) ^ i ≤ P * Q :=
      mul_le_mul hPlow hQlow (by positivity) (le_of_lt hPpos)
    have h4 : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by
      rw [← mul_pow]; norm_num
    refine le_trans (le_of_eq ?_) h1
    simp only [h2i, div_pow, h4]
    ring
  have hPQpos : 0 < P * Q := mul_pos hPpos hQpos
  have hPQsub : |P * Q - (N : ℝ) ^ (2 * i)| ≤ 2 * 4 ^ i * B * (N : ℝ) ^ (2 * i) / N := by
    have hsplit : P * Q - (N : ℝ) ^ (2 * i)
        = (P - (N : ℝ) ^ i) * Q + (N : ℝ) ^ i * (Q - (N : ℝ) ^ i) := by
      rw [h2i]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow, abs_of_pos hNpos]
    have hb1 : |P - (N : ℝ) ^ i| * |Q|
        ≤ (2 ^ i * B * (N : ℝ) ^ i / N) * (2 ^ i * (N : ℝ) ^ i) :=
      mul_le_mul hPsub hQabs (abs_nonneg _) (by positivity)
    have hb2 : (N : ℝ) ^ i * |Q - (N : ℝ) ^ i|
        ≤ (N : ℝ) ^ i * (2 ^ i * B * (N : ℝ) ^ i / N) := by
      exact mul_le_mul_of_nonneg_left hQsub (by positivity)
    have h4 : (2 : ℝ) ^ i * 2 ^ i = 4 ^ i := by
      rw [← mul_pow]; norm_num
    have h2le4 : (2 : ℝ) ^ i ≤ 4 ^ i := by
      apply pow_le_pow_left₀ (by norm_num) (by norm_num)
    calc |P - (N : ℝ) ^ i| * |Q| + (N : ℝ) ^ i * |Q - (N : ℝ) ^ i|
        ≤ (2 ^ i * B * (N : ℝ) ^ i / N) * (2 ^ i * (N : ℝ) ^ i)
          + (N : ℝ) ^ i * (2 ^ i * B * (N : ℝ) ^ i / N) := add_le_add hb1 hb2
    _ = (4 ^ i + 2 ^ i) * B * ((N : ℝ) ^ i * (N : ℝ) ^ i) / N := by
        rw [← h4]; ring
    _ ≤ 2 * 4 ^ i * B * (N : ℝ) ^ (2 * i) / N := by
        rw [h2i]
        gcongr
        linarith
  -- the exact decomposition of the target
  have hNe : (N : ℝ) ≠ 0 := hNpos.ne'
  have hkey : f i (N : ℝ) - f i ((N : ℝ) + (n : ℝ)) - i * n / (N : ℝ) ^ (i + 1)
      = (n : ℝ) * (S - i * ((N : ℝ) ^ i / N)) / (P * Q)
        + ((i : ℝ) * n) * (((N : ℝ) ^ i / N) * (N : ℝ) ^ (i + 1) - P * Q)
            / (P * Q * (N : ℝ) ^ (i + 1)) := by
    rw [hfP, hfQ, inv_sub_inv hPpos.ne' hQpos.ne', htel]
    field_simp
    ring
  rw [hkey]
  -- bound the two terms
  have habs : |(n : ℝ) * (S - i * ((N : ℝ) ^ i / N)) / (P * Q)
        + ((i : ℝ) * n) * (((N : ℝ) ^ i / N) * (N : ℝ) ^ (i + 1) - P * Q)
            / (P * Q * (N : ℝ) ^ (i + 1))|
      ≤ |(n : ℝ)| * |S - i * ((N : ℝ) ^ i / N)| / (P * Q)
        + ((i : ℝ) * |(n : ℝ)|) * |((N : ℝ) ^ i / N) * (N : ℝ) ^ (i + 1) - P * Q|
            / (P * Q * (N : ℝ) ^ (i + 1)) := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    have e1 : |(n : ℝ) * (S - i * ((N : ℝ) ^ i / N)) / (P * Q)|
        = |(n : ℝ)| * |S - i * ((N : ℝ) ^ i / N)| / (P * Q) := by
      rw [abs_div, abs_mul, abs_of_pos hPQpos]
    have e2 : |((i : ℝ) * n) * (((N : ℝ) ^ i / N) * (N : ℝ) ^ (i + 1) - P * Q)
          / (P * Q * (N : ℝ) ^ (i + 1))|
        = ((i : ℝ) * |(n : ℝ)|) * |((N : ℝ) ^ i / N) * (N : ℝ) ^ (i + 1) - P * Q|
          / (P * Q * (N : ℝ) ^ (i + 1)) := by
      rw [abs_div, abs_mul, abs_mul, Nat.abs_cast,
        abs_of_pos (show (0:ℝ) < P * Q * (N : ℝ) ^ (i + 1) by positivity)]
    rw [e1, e2]
  refine habs.trans ?_
  -- rewrite the center of the second numerator as N ^ (2i)
  have hcenter : ((N : ℝ) ^ i / N) * (N : ℝ) ^ (i + 1) = (N : ℝ) ^ (2 * i) := by
    rw [h2i]
    field_simp
    ring
  rw [hcenter]
  -- power-combination facts, each proved deterministically
  have hquot1 : (N : ℝ) ^ i / ((N : ℝ) ^ 2 * (N : ℝ) ^ (2 * i)) = 1 / (N : ℝ) ^ (i + 2) := by
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have hquot2 : (N : ℝ) ^ (2 * i) / ((N : ℝ) * ((N : ℝ) ^ (2 * i) * (N : ℝ) ^ (i + 1)))
      = 1 / (N : ℝ) ^ (i + 2) := by
    have h1 : (N : ℝ) ^ (i + 2) = N * (N : ℝ) ^ (i + 1) := by
      rw [← pow_succ']
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, h1]
    ring
  have hterm1 : |(n : ℝ)| * |S - i * ((N : ℝ) ^ i / N)| / (P * Q)
      ≤ (i : ℝ) * (2 ^ i * 4 ^ i) * (B * |(n : ℝ)|) / (N : ℝ) ^ (i + 2) := by
    calc |(n : ℝ)| * |S - i * ((N : ℝ) ^ i / N)| / (P * Q)
        ≤ |(n : ℝ)| * (i * (2 ^ i * B * ((N : ℝ) ^ i / N) / N))
            / ((N : ℝ) ^ (2 * i) / 4 ^ i) := by
          gcongr
    _ = (i : ℝ) * (2 ^ i * 4 ^ i) * (B * |(n : ℝ)|)
          * ((N : ℝ) ^ i / ((N : ℝ) ^ 2 * (N : ℝ) ^ (2 * i))) := by
          field_simp
    _ = (i : ℝ) * (2 ^ i * 4 ^ i) * (B * |(n : ℝ)|) / (N : ℝ) ^ (i + 2) := by
          rw [hquot1]
          ring
  have hterm2 : ((i : ℝ) * |(n : ℝ)|) * |(N : ℝ) ^ (2 * i) - P * Q|
        / (P * Q * (N : ℝ) ^ (i + 1))
      ≤ 2 * (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|) / (N : ℝ) ^ (i + 2) := by
    calc ((i : ℝ) * |(n : ℝ)|) * |(N : ℝ) ^ (2 * i) - P * Q|
          / (P * Q * (N : ℝ) ^ (i + 1))
        ≤ ((i : ℝ) * |(n : ℝ)|) * (2 * 4 ^ i * B * (N : ℝ) ^ (2 * i) / N)
            / (((N : ℝ) ^ (2 * i) / 4 ^ i) * (N : ℝ) ^ (i + 1)) := by
          have hPQsub' : |(N : ℝ) ^ (2 * i) - P * Q|
              ≤ 2 * 4 ^ i * B * (N : ℝ) ^ (2 * i) / N := by
            rw [abs_sub_comm]; exact hPQsub
          gcongr
    _ = 2 * (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|)
          * ((N : ℝ) ^ (2 * i) / ((N : ℝ) * ((N : ℝ) ^ (2 * i) * (N : ℝ) ^ (i + 1)))) := by
          field_simp
    _ = 2 * (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|) / (N : ℝ) ^ (i + 2) := by
          rw [hquot2]
          ring
  refine (add_le_add hterm1 hterm2).trans ?_
  -- final numeric comparison of the constants
  have h16 : (16 : ℝ) ^ i = 4 ^ i * 4 ^ i := by
    rw [← mul_pow]; norm_num
  have h2le4 : (2 : ℝ) ^ i ≤ 4 ^ i :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) i
  have hBn : B * |(n : ℝ)| ≤ ((i : ℝ) + 1) * (n : ℝ) ^ 2 := by
    have hsq : |(n : ℝ)| * |(n : ℝ)| = (n : ℝ) ^ 2 := by
      rw [← abs_mul, abs_mul_self]
      ring
    have hle : B ≤ ((i : ℝ) + 1) * |(n : ℝ)| := by
      have hkey : (0:ℝ) ≤ (i : ℝ) * (|(n : ℝ)| - 1) :=
        mul_nonneg (by linarith) (by linarith)
      rw [hBdef]
      nlinarith [hkey]
    calc B * |(n : ℝ)| ≤ (((i : ℝ) + 1) * |(n : ℝ)|) * |(n : ℝ)| := by
          exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
    _ = ((i : ℝ) + 1) * (n : ℝ) ^ 2 := by rw [mul_assoc, hsq]
  rw [← add_div, h16]
  have hbn0 : (0 : ℝ) ≤ B * |(n : ℝ)| := mul_nonneg hB0 (abs_nonneg _)
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have h24 : (2 : ℝ) ^ i * 4 ^ i ≤ 4 ^ i * 4 ^ i :=
    mul_le_mul_of_nonneg_right h2le4 (by positivity)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc (i : ℝ) * (2 ^ i * 4 ^ i) * (B * |(n : ℝ)|)
        + 2 * (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|)
      ≤ (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|)
        + 2 * (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h24 hi0) hbn0
        linarith
  _ = 3 * (i : ℝ) * (4 ^ i * 4 ^ i) * (B * |(n : ℝ)|) := by ring
  _ ≤ 3 * (i : ℝ) * (4 ^ i * 4 ^ i) * (((i : ℝ) + 1) * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hBn (by positivity)
  _ ≤ 3 * ((i : ℝ) + 1) ^ 2 * (4 ^ i * 4 ^ i) * (n : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg
        (show (0:ℝ) ≤ 3 * (4 ^ i * 4 ^ i) by positivity) (sq_nonneg (n : ℝ)))
        (show (0:ℝ) ≤ (i : ℝ) + 1 by positivity)]
end Erdos266
