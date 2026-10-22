-- Prove2me | solution 1 for GDGen3.rootXi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:30:20.290676+00:00
-- url     : https://prove2.me/submissions/b77ce4ab-cb9a-49e3-9b2b-87892a3a08d4

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootXi_nonneg

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

lemma PiS_next_strict (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (n : ℕ) (hn : 0 < n) :
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

lemma PiS_average_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => PiS r (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have ht := PiS_next_strict r hr hr1 (n + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at ht ⊢
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  simp only [PiS, sum_range_succ] at *
  nlinarith

lemma X_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : 1 ≤ i) (hiN : i < N) :
    0 < X r N i := by
  have hNi : 1 ≤ N := by omega
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hNi
  have hm := PiS_average_strictMono r hr hr1 (by omega : i - 1 < N - 1)
  dsimp at hm
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hNi] at hm
  have hci2 : ((i - 1 : ℕ) : ℝ) + 2 = (i : ℝ) + 1 := by linarith
  have hcN2 : ((N - 1 : ℕ) : ℝ) + 2 = (N : ℝ) + 1 := by linarith
  rw [hci, hcN, hci2, hcN2] at hm
  have hipos : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc := (div_lt_div_iff₀ (by positivity) (by positivity)).mp hm
  unfold X M
  apply div_pos
  · have hden : 0 < (N : ℝ) * ((N : ℝ) + 1) := by positivity
    have hnum : 0 < (1 - r) *
        ((i : ℝ) * ((i : ℝ) + 1) * PiS r N - (N : ℝ) * ((N : ℝ) + 1) * PiS r i) :=
      mul_pos (by linarith) (by nlinarith [hc])
    have he : 2 * (1 - r) * PiS r N / ((N : ℝ) * ((N : ℝ) + 1)) * (i : ℝ) * ((i : ℝ) + 1) / 2
        - (1 - r) * PiS r i =
        ((1 - r) * ((i : ℝ) * ((i : ℝ) + 1) * PiS r N - (N : ℝ) * ((N : ℝ) + 1) * PiS r i)) /
          ((N : ℝ) * ((N : ℝ) + 1)) := by field_simp
    rw [he]
    exact div_pos hnum hden
  · positivity

lemma rootXi_zero (r : ℝ) (N : ℕ) : rootXi r N 0 = 0 := by simp [rootXi]

lemma rootXi_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hi : i ≠ 0) :
    0 < rootXi r N i := by
  unfold rootXi
  rw [if_neg hi]
  by_cases hiN : i < N
  · rw [if_pos hiN]
    have hx := X_pos r hr hr1 N i (by omega) hiN
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hdisc : (1 + C r N i) ^ 2 < (1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1) := by
      have hd : 0 < 4 * X r N i / pj r (i + 1) := div_pos (by positivity) hp
      linarith
    have hsq : |1 + C r N i| < Real.sqrt ((1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1)) := by
      rw [← Real.sqrt_sq_eq_abs (1 + C r N i)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hdisc
    have hb := le_abs_self (1 + C r N i)
    linarith
  · simp [hiN]

end GDGen3Proof_rootXi_nonneg

open GDGen3Proof_rootXi_nonneg

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) : 0 ≤ rootXi r N i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero]
  · exact le_of_lt (rootXi_pos r hr hr1 N i hi)
