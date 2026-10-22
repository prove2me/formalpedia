-- Prove2me | solution 1 for GDGen3.rootXi_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:39:13.216888+00:00
-- url     : https://prove2.me/submissions/1244630f-00c5-41fd-9497-1320e5e72c64

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase

noncomputable section

open Finset

open GDGen3

namespace GDGen3Proof_rootXi_step_bound

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

lemma pj_step (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    r ^ 2 * pj r (i + 1) - pj r i = (1 - r ^ 2) / 2 := by
  simp only [pj, Nat.mul_add, pow_add]
  field_simp
  ring

lemma PiS_closed (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    PiS r i = pj r i / (1 - r ^ 2) - (i : ℝ) / 2 := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hne : 1 - r ^ 2 ≠ 0 := by linarith
  induction i with
  | zero => simp [PiS, pj]
  | succ i ih =>
    have hp := pj_step r (ne_of_gt hr) i
    change PiS r (i + 1) = _
    rw [PiS, sum_range_succ]
    change PiS r i + pj r (i + 1) = _
    rw [ih]
    push_cast
    field_simp [hne]
    nlinarith [hp]

lemma X_zero (r : ℝ) (N : ℕ) : X r N 0 = 0 := by simp [X, PiS]

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

lemma X_step (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) :
    X r N (i + 1) - X r N i = pj r (i + 1) * C r N i := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold X C
  rw [PiS, sum_range_succ]
  change (M r N * ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) / 2
      - (1 - r) * (PiS r i + pj r (i + 1))) / (1 + r)
    - (M r N * (i : ℝ) * ((i : ℝ) + 1) / 2 - (1 - r) * PiS r i) / (1 + r) = _
  push_cast
  field_simp [hp]
  ring

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

lemma rootXi_quad (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * rootXi r N i * (1 + eta r N (rootXi r N) i) = X r N i := by
  by_cases hi : i = 0
  · subst i; simp [rootXi_zero, X_zero]
  · have hx := X_pos r hr hr1 N i (by omega) hiN
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hd : 0 ≤ (1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1) := by positivity
    have hs := Real.sq_sqrt hd
    unfold eta
    simp only [rootXi, if_neg hi, if_pos hiN]
    have hm : pj r (i + 1) * (4 * X r N i / pj r (i + 1)) = 4 * X r N i :=
      mul_div_cancel₀ _ (ne_of_gt hp)
    nlinarith [hs, hm]

lemma rootXi_quad7 (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) (hiN : i < N) :
    pj r (i + 1) * eta r N (rootXi r N) i * (1 + rootXi r N i) = X r N (i + 1) := by
  have hq := rootXi_quad r hr hr1 N i hiN
  have hx := X_step r hr hr1 N i
  unfold eta at *
  linear_combination hq - hx

lemma rootXi_nonneg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ) : 0 ≤ rootXi r N i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero]
  · exact le_of_lt (rootXi_pos r hr hr1 N i hi)

lemma M_gap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N) :
    (1 + r) - M r N =
      ((1 + (N : ℝ) * (1 + r)) ^ 2 - 1 / r ^ (2 * N)) /
        ((1 + r) * (N : ℝ) * ((N : ℝ) + 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  unfold M
  rw [PiS_closed r hr hr1 N]
  unfold pj
  field_simp
  ring

lemma M_le_h (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : M r N ≤ 1 + r := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb : (1 / r ^ N) ^ 2 ≤ (1 + (N : ℝ) * (1 + r)) ^ 2 := by
    have hi : 0 ≤ 1 / r ^ N := by positivity
    nlinarith
  have he : (1 / r ^ N) ^ 2 = 1 / r ^ (2 * N) := by
    rw [Nat.mul_comm 2 N, pow_mul, div_pow, one_pow]
  rw [he] at hb
  have hgap : 0 ≤ (1 + r) - M r N := by
    rw [M_gap r hr hr1 N hN]
    apply div_nonneg (by linarith) (by positivity)
  linarith

lemma referenceXi_zero (r : ℝ) (hr : 0 < r) : referenceXi r 0 = 0 := by simp [referenceXi]

lemma reference_power_bound (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    1 / r ^ i < 1 + (i : ℝ) * (1 + r) := by
  have hz : 1 < 1 / r := (lt_div_iff₀ hr).2 (by simpa using hr1)
  have hs := pow_slope_strictMono (1 / r) hz (by omega : i - 1 < N - 1)
  dsimp at hs
  have hN : 1 ≤ N := by omega
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hN] at hs
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  have hcN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast Nat.sub_add_cancel hN
  rw [hci, hcN, div_pow, div_pow, one_pow, one_pow] at hs
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs' := (div_lt_div_iff₀ hip hNp).mp hs
  have hm := mul_le_mul_of_nonneg_left hbranch (le_of_lt hip)
  nlinarith

lemma referenceXi_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) : 0 < referenceXi r i := by
  have h := reference_power_bound r hr hr1 N i hi hiN hbranch
  unfold referenceXi
  exact div_pos (by linarith) (by positivity)

lemma referenceXi_lt_half (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    referenceXi r i < (i : ℝ) / 2 := by
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hri : 1 < 1 / r ^ i := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ i)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i ≠ 0)
  have hri1 : 1 < 1 / r ^ (i + 1) := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ (i + 1))).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
  unfold referenceXi
  apply (div_lt_iff₀ (by positivity : 0 < (1 + r) * (1 + 1 / r ^ (i + 1)))).2
  have hm := mul_pos hip (show 0 < (1 + r) * (1 / r ^ (i + 1) - 1) by positivity)
  nlinarith

lemma rootPoly_expanded (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = pj r (i + 1) * x * (1 + x - (1 - r) / (1 + r))
      + v * (i + 1) * x / (1 + r) - v * (i : ℝ) * (i + 1) / (2 * (1 + r))
      + (1 - r) * PiS r i / (1 + r) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring

lemma referenceXi_quad (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    rootPoly r (1 + r) i (referenceXi r i) = 0 := by
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  rw [rootPoly_expanded r hr hr1]
  unfold referenceXi
  rw [PiS_closed r hr hr1 i]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1, pow_succ r i]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hbp : 1 - (b * r) ^ 2 ≠ 0 := by
    have ht : r ^ (2 * (i + 1)) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    rw [he1] at ht
    change (b * r) ^ 2 < 1 at ht
    linarith
  field_simp [hbp]
  ring

lemma rootPoly_parameter (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (v x : ℝ) (i : ℕ) :
    rootPoly r v i x = rootPoly r (1 + r) i x
      + ((1 + r) - v) * (i + 1) / (1 + r) * ((i : ℝ) / 2 - x) := by
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootPoly
  field_simp [hp]
  ring

lemma rootPoly_actual (r : ℝ) (N i : ℕ) (x : ℝ) :
    rootPoly r (M r N) i x = pj r (i + 1) * x * (1 + x + C r N i) - X r N i := by
  unfold rootPoly C X
  ring

lemma quadratic_root_le (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 ≤ p * y ^ 2 + b * y - X) : x ≤ y := by
  by_contra hle
  have hxy : y - x < 0 := by linarith
  have hpos : 0 < p * x * y + X := by positivity
  have he : x * (p * y ^ 2 + b * y - X) = (y - x) * (p * x * y + X) := by
    linear_combination y * hroot
  have hneg := mul_neg_of_neg_of_pos hxy hpos
  have hnon := mul_nonneg (le_of_lt hx) hq
  rw [he] at hnon
  linarith

lemma quadratic_root_lt (p b X x y : ℝ) (hp : 0 < p) (hX : 0 < X)
    (hx : 0 < x) (hy : 0 ≤ y)
    (hroot : p * x ^ 2 + b * x - X = 0) (hq : 0 < p * y ^ 2 + b * y - X) : x < y := by
  have hle := quadratic_root_le p b X x y hp hX hx hy hroot (le_of_lt hq)
  have hne : x ≠ y := by intro he; subst y; linarith
  exact lt_of_le_of_ne hle hne

lemma rootXi_le_reference (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hiN : i < N) (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    rootXi r N i ≤ referenceXi r i := by
  by_cases hi : i = 0
  · subst i; rw [rootXi_zero, referenceXi_zero r hr]
  · have hi1 : 1 ≤ i := by omega
    have hp := pj_pos r hr hr1 (i + 1) (by omega)
    have hx := X_pos r hr hr1 N i hi1 hiN
    have hxi := rootXi_pos r hr hr1 N i hi
    have href := referenceXi_pos r hr hr1 N i hi1 hiN hbranch
    have hm := M_le_h r hr hr1 N (by omega) hbranch
    have hhalf := referenceXi_lt_half r hr hr1 i hi1
    have hpoly : 0 ≤ rootPoly r (M r N) i (referenceXi r i) := by
      rw [rootPoly_parameter r hr hr1, referenceXi_quad r hr hr1, zero_add]
      apply mul_nonneg
      · apply div_nonneg (by positivity) (by positivity)
      · linarith
    rw [rootPoly_actual] at hpoly
    have hroot := rootXi_quad r hr hr1 N i hiN
    unfold eta at hroot
    apply quadratic_root_le (pj r (i + 1)) (pj r (i + 1) * (1 + C r N i)) (X r N i)
      (rootXi r N i) (referenceXi r i) hp hx hxi (le_of_lt href)
    · nlinarith [hroot]
    · nlinarith [hpoly]

lemma rootNu_neg (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : rootNu r i < 0 := by
  have h := pj_slope_strictMono r hr hr1 (by omega : i - 1 < i)
  dsimp at h
  rw [Nat.sub_add_cancel hi] at h
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  rw [hci] at h
  have hip : 0 < (i : ℝ) := by exact_mod_cast (show 0 < i by omega)
  have hp := pj_pos r hr hr1 i (by omega)
  have hp1 := pj_pos r hr hr1 (i + 1) (by omega)
  have hc := (div_lt_div_iff₀ hip (by positivity)).mp h
  unfold rootNu
  apply sub_neg.mpr
  apply (div_lt_div_iff₀ hp1 hp).2
  nlinarith

lemma pj_strictMono (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : StrictMono (pj r) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : 2 ≠ 0)
  intro a b hab
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  exact div_lt_div_of_pos_right (sub_lt_sub_right (pow_lt_pow_right₀ hz hab) 1) (by norm_num)

lemma rootE_one (r : ℝ) (hr : 0 < r) : rootE r 1 = (1 + r) * (1 - r) ^ 2 / r := by
  unfold rootE
  norm_num only [pow_one, Nat.cast_one]
  field_simp
  ring

lemma rootE_step (r : ℝ) (hr : 0 < r) (i : ℕ) :
    rootE r (i + 1) - rootE r i = (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
  unfold rootE
  push_cast
  rw [pow_succ r i]
  field_simp
  ring

lemma rootE_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) : 0 < rootE r i := by
  induction i, hi using Nat.le_induction with
  | base =>
    rw [rootE_one r hr]
    have hd : 0 < 1 - r := by linarith
    positivity
  | succ i hi ih =>
    have hp : 1 < 1 / r ^ (i + 1) := by
      apply (lt_div_iff₀ (pow_pos hr _)).2
      simpa using pow_lt_one₀ (le_of_lt hr) hr1 (by omega : i + 1 ≠ 0)
    have hstep := rootE_step r hr i
    have hg : 0 < (1 + r) * (1 - r) * (1 / r ^ (i + 1) - 1) := by
      have hd : 0 < 1 - r := by linarith
      have hp' : 0 < 1 / r ^ (i + 1) - 1 := by linarith
      positivity
    linarith

lemma rootJ_reference_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    rootJ r (1 + r) (referenceXi r (i - 1)) i =
      r ^ i * rootE r i / ((1 - r ^ i) * (1 - (r ^ i * r) ^ 2)) := by
  have hprev : r ^ (i - 1) = r ^ i / r := by
    apply (eq_div_iff (ne_of_gt hr)).2
    rw [← pow_succ, Nat.sub_add_cancel hi]
  have hci : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    have hplus : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
    linarith
  have hpi : pj r i ≠ 0 := ne_of_gt (pj_pos r hr hr1 i (by omega))
  have hpi1 : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  unfold rootJ rootNu referenceXi rootE
  rw [Nat.sub_add_cancel hi, hprev, hci]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hblt : b < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hbrlt : b * r < 1 := by nlinarith
  have hbrpos : 0 < b * r := by positivity
  have hbnz : 1 - b ≠ 0 := by linarith
  have hbne : 1 - b ^ 2 ≠ 0 := by nlinarith
  have hbrne : 1 - (b * r) ^ 2 ≠ 0 := by nlinarith
  have hbrne' : 1 - b ^ 2 * r ^ 2 ≠ 0 := by convert hbrne using 1 <;> ring
  field_simp [hbnz, hbne, hbrne, hbrne']
  ring

lemma rootJ_reference_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) (hi : 1 ≤ i) :
    0 < rootJ r (1 + r) (referenceXi r (i - 1)) i := by
  rw [rootJ_reference_factor r hr hr1 i hi]
  have hp : 0 < r ^ i := pow_pos hr i
  have hi1 : r ^ i < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
  have hp1 : r ^ i * r < 1 := by nlinarith
  have hp1pos : 0 < r ^ i * r := by positivity
  have hden : 0 < (1 - r ^ i) * (1 - (r ^ i * r) ^ 2) := by
    have hd1 : 0 < 1 - r ^ i := by linarith
    have hd2 : 0 < 1 - (r ^ i * r) ^ 2 := by nlinarith
    positivity
  exact div_pos (mul_pos hp (rootE_pos r hr hr1 i hi)) hden

lemma rootJ_actual_pos (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    0 < rootJ r (M r N) (rootXi r N (i - 1)) i := by
  have href := rootJ_reference_pos r hr hr1 i hi
  have hxi := rootXi_le_reference r hr hr1 N (i - 1) (by omega) hbranch
  have hm := M_le_h r hr hr1 N (by omega) hbranch
  have hnu := rootNu_neg r hr hr1 i hi
  have hpp := pj_strictMono r hr hr1 (by omega : i < i + 1)
  have hp1 := pj_pos r hr hr1 (i + 1) (by omega)
  have hk : 0 < 1 - pj r i / pj r (i + 1) := by
    apply sub_pos.mpr
    exact (div_lt_one hp1).2 hpp
  have hmdiv : M r N / (1 + r) ≤ 1 := (div_le_one (by positivity)).2 hm
  have hnu2 := mul_le_mul_of_nonpos_right hmdiv (le_of_lt hnu)
  have hxi2 := mul_le_mul_of_nonneg_left hxi (le_of_lt hk)
  unfold rootJ at *
  have hh : (1 + r) / (1 + r) = (1 : ℝ) := div_self (by positivity)
  rw [hh] at href
  nlinarith

lemma rootPoly_factor (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N) :
    rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) =
      pj r i * (1 + rootXi r N (i - 1)) * rootJ r (M r N) (rootXi r N (i - 1)) i := by
  have hq := rootXi_quad7 r hr hr1 N (i - 1) (by omega)
  rw [Nat.sub_add_cancel hi] at hq
  have hp : pj r i ≠ 0 := ne_of_gt (pj_pos r hr hr1 i (by omega))
  have hp1 : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  have hci : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast Nat.sub_add_cancel hi
  rw [rootPoly_actual, ← hq]
  unfold eta C rootJ rootNu
  rw [Nat.sub_add_cancel hi, hci]
  field_simp [hp, hp1]
  ring

end GDGen3Proof_rootXi_step_bound

open GDGen3Proof_rootXi_step_bound

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N i : ℕ)
    (hi : 1 ≤ i) (hiN : i < N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r)) :
    rootXi r N i < pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1)) := by
  have hp := pj_pos r hr hr1 (i + 1) (by omega)
  have hpi := pj_pos r hr hr1 i (by omega)
  have hxp := rootXi_pos r hr hr1 N i (by omega)
  have hx := X_pos r hr hr1 N i hi hiN
  have hprev := rootXi_nonneg r hr hr1 N (i - 1)
  have hj := rootJ_actual_pos r hr hr1 N i hi hiN hbranch
  have hy : 0 < pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1)) := by positivity
  have hpoly : 0 < rootPoly r (M r N) i (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) := by
    rw [rootPoly_factor r hr hr1 N i hi hiN]
    positivity
  rw [rootPoly_actual] at hpoly
  have hroot := rootXi_quad r hr hr1 N i hiN
  unfold eta at hroot
  apply quadratic_root_lt (pj r (i + 1)) (pj r (i + 1) * (1 + C r N i)) (X r N i)
    (rootXi r N i) (pj r i / pj r (i + 1) * (1 + rootXi r N (i - 1))) hp hx hxp (le_of_lt hy)
  · nlinarith [hroot]
  · nlinarith [hpoly]
