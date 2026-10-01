-- Prove2me | solution 1 for Erdos287.n0_two_impossible
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:09:10.687743+00:00
-- url     : https://prove2.me/submissions/34164550-84e3-4217-942c-acbe1f315fa5

import Mathlib

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : Finset.sum (Finset.range k) (fun i => (1 : ℚ) / (f i : ℚ)) = 1)
    (hgap : ∀ i, i + 1 < k → f (i + 1) - f i ≤ 2)
    (hf0 : f 0 = 2) :
    False  := by
  have h01 := hmono 0 1 (by omega) (by omega)
  have hg01 := hgap 0 (by omega)
  norm_num at hg01
  have h1 : f 1 = 3 ∨ f 1 = 4 := by omega
  have hk4 : k < 4 := by
    by_contra hn
    have hk4 : 4 ≤ k := by omega
    have hg12 := hgap 1 (by omega)
    have hg23 := hgap 2 (by omega)
    norm_num at hg12 hg23
    have hm12 := hmono 1 2 (by omega) (by omega)
    have hm23 := hmono 2 3 (by omega) (by omega)
    have hb1 : f 1 ≤ 4 := by omega
    have hb2 : f 2 ≤ 6 := by omega
    have hb3 : f 3 ≤ 8 := by omega
    have hrec (i n : ℕ) (hi : i < k) (hin : f i ≤ n) :
        (1 : ℚ) / n ≤ 1 / f i := by
      apply one_div_le_one_div_of_le
      · exact_mod_cast (lt_trans (by norm_num : 0 < 1) (hf1 i hi))
      · exact_mod_cast hin
    have hsum4 := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun i => (1 : ℚ) / (f i : ℚ)) (Finset.range_mono hk4)
      (fun i _ _ => by positivity)
    rw [hsum] at hsum4
    norm_num [Finset.sum_range_succ, hf0] at hsum4
    have h11 := hrec 1 4 (by omega) hb1
    have h22 := hrec 2 6 (by omega) hb2
    have h33 := hrec 3 8 (by omega) hb3
    norm_num at h11 h22 h33
    linarith
  have hkcase : k = 2 ∨ k = 3 := by omega
  rcases hkcase with rfl | rfl
  · rcases h1 with h1 | h1 <;> norm_num [Finset.sum_range_succ, hf0, h1] at hsum
  · have hm12 := hmono 1 2 (by omega) (by omega)
    have hg12 := hgap 1 (by omega)
    norm_num at hg12
    have h2 : f 2 = 4 ∨ f 2 = 5 ∨ f 2 = 6 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
      norm_num [Finset.sum_range_succ, hf0, h1, h2] at hsum

    all_goals omega
