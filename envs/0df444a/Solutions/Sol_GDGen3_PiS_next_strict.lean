-- Prove2me | solution 1 for GDGen3.PiS_next_strict
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:25:45.867833+00:00
-- url     : https://prove2.me/submissions/07937123-8a6d-426d-abfc-c7ccd644a77b

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_PiS_next_strict

lemma pj_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (j : ℕ) (hj : j ≠ 0) :
    0 < pj r j := by
  have ht : r ^ (2 * j) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  exact div_pos (by linarith) (by positivity)

lemma pj_geometric (r : ℝ) (hr : r ≠ 0) (j : ℕ) :
    pj r j = ((1 / r ^ 2) ^ j - 1) / 2 := by
  unfold pj
  simp only [div_pow, one_pow, ← pow_mul]
  field_simp

lemma pow_slope_strictMono (z : ℝ) (hz : 1 < z) :
    StrictMono (fun n : ℕ => (z ^ (n + 1) - 1) / ((n : ℝ) + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hsum : (∑ k ∈ range (n + 1), z ^ k) < ((n : ℝ) + 1) * z ^ (n + 1) := by
    calc
      _ < ∑ k ∈ range (n + 1), z ^ (n + 1) := by
        apply sum_lt_sum
        · intro k hk; exact le_of_lt (pow_lt_pow_right₀ hz (mem_range.mp hk))
        · exact ⟨0, by simp, pow_lt_pow_right₀ hz (by omega)⟩
      _ = _ := by simp
  have hm := mul_lt_mul_of_pos_right hsum (by linarith : 0 < z - 1)
  rw [geom_sum_mul] at hm
  apply (div_lt_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ) + 1)).2
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  rw [pow_succ] at hm
  nlinarith

lemma pj_slope_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => pj r (n + 1) / ((n : ℝ) + 1)) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    simpa using ht
  intro a b hab
  have h := pow_slope_strictMono (1 / r ^ 2) hz hab
  dsimp at h ⊢
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  have he : ∀ k : ℕ, (((1 / r ^ 2) ^ (k + 1) - 1) / 2) / ((k : ℝ) + 1) =
      (((1 / r ^ 2) ^ (k + 1) - 1) / ((k : ℝ) + 1)) / 2 := by intro k; ring
  rw [he, he]
  exact div_lt_div_of_pos_right h (by norm_num)

lemma nat_prefix_weight (n : ℕ) :
    2 * (∑ k ∈ range n, ((k : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

end GDGen3Proof_PiS_next_strict

open GDGen3Proof_PiS_next_strict

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) (hn : 0 < n) :
    2 * PiS r n < (n : ℝ) * pj r (n + 1) := by
  have ht : ∀ k ∈ range n,
      pj r (k + 1) * ((n : ℝ) + 1) < pj r (n + 1) * ((k : ℝ) + 1) := by
    intro k hk
    have h := pj_slope_strictMono r hr hr1 (mem_range.mp hk)
    exact (div_lt_div_iff₀ (by positivity) (by positivity)).mp h
  have hsum : (∑ k ∈ range n, pj r (k + 1) * ((n : ℝ) + 1)) <
      ∑ k ∈ range n, pj r (n + 1) * ((k : ℝ) + 1) := by
    apply sum_lt_sum
    · intro k hk; exact le_of_lt (ht k hk)
    · exact ⟨0, mem_range.mpr hn, ht 0 (mem_range.mpr hn)⟩
  rw [← sum_mul, ← mul_sum] at hsum
  have hw := nat_prefix_weight n
  change PiS r n * ((n : ℝ) + 1) < pj r (n + 1) * _ at hsum
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hmul : (2 * PiS r n - (n : ℝ) * pj r (n + 1)) * ((n : ℝ) + 1) < 0 := by
    nlinarith [mul_nonneg (le_of_lt (pj_pos r hr hr1 (n + 1) (by omega))) (le_of_lt hnpos)]
  have hd : 2 * PiS r n - (n : ℝ) * pj r (n + 1) < 0 := by
    by_contra hneg
    have hnon := mul_nonneg (le_of_not_gt hneg) (le_of_lt hnpos)
    linarith
  exact sub_neg.mp hd
