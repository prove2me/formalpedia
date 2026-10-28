-- Prove2me | solution 1 for FastCLO.LowerBound.binomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T04:41:32.43074+00:00
-- url     : https://prove2.me/submissions/e5900293-2939-4924-8359-ff5f4650a55e

import Mathlib

namespace Prove2SwarmSubmission

namespace FastCLO.LowerBound

open Finset

lemma inner_weight_sum (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ) / (2 : ℝ) ^ k) = 1 := by
  rw [← Finset.sum_div]
  have h : (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ)) = (2 : ℝ) ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [h]
  field_simp

lemma sum_range_sq_mul_choose (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (j : ℝ) ^ 2 * (Nat.choose k j : ℝ)) =
      (k : ℝ) * ((k : ℝ) + 1) * (2 : ℝ) ^ k / 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hshift :
          (∑ j ∈ Finset.range (k + 2), (j : ℝ) ^ 2 * (Nat.choose (k + 1) j : ℝ)) =
            (∑ j ∈ Finset.range (k + 1),
              ((j : ℝ) + 1) ^ 2 * (Nat.choose (k + 1) (j + 1) : ℝ)) := by
        rw [Finset.sum_range_succ']
        simp
      have hchoose : ∀ j : ℕ,
          (Nat.choose (k + 1) (j + 1) : ℝ) =
            (Nat.choose k j : ℝ) + (Nat.choose k (j + 1) : ℝ) := by
        intro j
        exact_mod_cast Nat.choose_succ_succ' k j
      calc
        (∑ j ∈ Finset.range (k + 2), (j : ℝ) ^ 2 * (Nat.choose (k + 1) j : ℝ))
            = ∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) ^ 2 *
                  ((Nat.choose k j : ℝ) + (Nat.choose k (j + 1) : ℝ)) := by
              rw [hshift]
              apply Finset.sum_congr rfl
              intro j hj
              rw [hchoose j]
        _ = (∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) ^ 2 * (Nat.choose k j : ℝ)) +
              (∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) ^ 2 * (Nat.choose k (j + 1) : ℝ)) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = ((∑ j ∈ Finset.range (k + 1), (j : ℝ) ^ 2 * (Nat.choose k j : ℝ)) +
              2 * (∑ j ∈ Finset.range (k + 1), (j : ℝ) * (Nat.choose k j : ℝ)) +
              (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ))) +
              (∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) ^ 2 * (Nat.choose k (j + 1) : ℝ)) := by
              congr 1
              calc
                (∑ j ∈ Finset.range (k + 1),
                    ((j : ℝ) + 1) ^ 2 * (Nat.choose k j : ℝ))
                    = ∑ j ∈ Finset.range (k + 1),
                        ((j : ℝ) ^ 2 * (Nat.choose k j : ℝ) +
                          2 * ((j : ℝ) * (Nat.choose k j : ℝ)) +
                          (Nat.choose k j : ℝ)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                _ = _ := by
                      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        _ = ((∑ j ∈ Finset.range (k + 1), (j : ℝ) ^ 2 * (Nat.choose k j : ℝ))) +
              2 * ((k : ℝ) * (2 : ℝ) ^ (k - 1)) +
              (2 : ℝ) ^ k +
              (∑ j ∈ Finset.range (k + 1),
                ((j : ℝ) + 1) ^ 2 * (Nat.choose k (j + 1) : ℝ)) := by
              have hmul :
                  (∑ j ∈ Finset.range (k + 1), (j : ℝ) * (Nat.choose k j : ℝ)) =
                    (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
                exact_mod_cast Nat.sum_range_mul_choose k
              have hsum :
                  (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ)) =
                    (2 : ℝ) ^ k := by
                exact_mod_cast Nat.sum_range_choose k
              rw [hmul, hsum]
        _ = _ := by
              have hS2 :
                  (∑ j ∈ Finset.range (k + 1),
                    ((j : ℝ) + 1) ^ 2 * (Nat.choose k (j + 1) : ℝ)) =
                    (∑ j ∈ Finset.range (k + 1), (j : ℝ) ^ 2 * (Nat.choose k j : ℝ)) := by
                rw [Finset.sum_range_succ]
                simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, add_zero]
                rw [Finset.sum_range_succ']
                simp
              rw [hS2, ih]
              by_cases hk : k = 0
              · subst k
                norm_num
              · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)
                have hpow : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
                  rw [pow_sub₀ (2 : ℝ) (by norm_num) hk1]
                  ring
                rw [hpow]
                push_cast
                ring

lemma sum_range_mul_choose_real (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (j : ℝ) * (Nat.choose k j : ℝ)) =
      (k : ℝ) * (2 : ℝ) ^ (k - 1) := by
  exact_mod_cast Nat.sum_range_mul_choose k

lemma sum_range_choose_real (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (Nat.choose k j : ℝ)) = (2 : ℝ) ^ k := by
  exact_mod_cast Nat.sum_range_choose k

lemma inner_second_moment (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (Nat.choose k j : ℝ) / (2 : ℝ) ^ k * (2 * (j : ℝ) - (k : ℝ)) ^ 2) = (k : ℝ) := by
  have hweighted :
      (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) / (2 : ℝ) ^ k * (2 * (j : ℝ) - (k : ℝ)) ^ 2) =
        (∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) * (2 * (j : ℝ) - (k : ℝ)) ^ 2) / (2 : ℝ) ^ k := by
    calc
      (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) / (2 : ℝ) ^ k * (2 * (j : ℝ) - (k : ℝ)) ^ 2) =
          ∑ j ∈ Finset.range (k + 1),
            ((Nat.choose k j : ℝ) * (2 * (j : ℝ) - (k : ℝ)) ^ 2) / (2 : ℝ) ^ k := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := (Finset.sum_div (Finset.range (k + 1))
        (fun j => (Nat.choose k j : ℝ) * (2 * (j : ℝ) - (k : ℝ)) ^ 2)
        ((2 : ℝ) ^ k)).symm
  have hnum :
      (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) * (2 * (j : ℝ) - (k : ℝ)) ^ 2) =
        4 * (∑ j ∈ Finset.range (k + 1),
          (j : ℝ) ^ 2 * (Nat.choose k j : ℝ)) -
        4 * (k : ℝ) * (∑ j ∈ Finset.range (k + 1),
          (j : ℝ) * (Nat.choose k j : ℝ)) +
        (k : ℝ) ^ 2 * (∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ)) := by
    calc
      (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) * (2 * (j : ℝ) - (k : ℝ)) ^ 2) =
          ∑ j ∈ Finset.range (k + 1),
            (4 * ((j : ℝ) ^ 2 * (Nat.choose k j : ℝ)) -
             4 * (k : ℝ) * ((j : ℝ) * (Nat.choose k j : ℝ)) +
             (k : ℝ) ^ 2 * (Nat.choose k j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [hweighted, hnum, sum_range_sq_mul_choose,
    sum_range_mul_choose_real, sum_range_choose_real]
  by_cases hk : k = 0
  · subst k
    norm_num
  · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)
    have hpow : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
      rw [pow_sub₀ (2 : ℝ) (by norm_num) hk1]
      ring
    rw [hpow]
    field_simp [pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]
    ring

lemma weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * f i) ^ 2 ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, w i * (f i) ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * f i)
  have hleft :
      (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * f i)) =
        ∑ i ∈ s, w i * f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw i hi)]
  have hright₁ :
      (∑ i ∈ s, (Real.sqrt (w i)) ^ 2) = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.sq_sqrt (hw i hi)]
  have hright₂ :
      (∑ i ∈ s, (Real.sqrt (w i) * f i) ^ 2) =
        ∑ i ∈ s, w i * (f i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [hleft, hright₁, hright₂] at h
  exact h

lemma inner_abs_bound (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
      (Nat.choose k j : ℝ) / (2 : ℝ) ^ k * |2 * (j : ℝ) - (k : ℝ)|) ≤
      Real.sqrt (k : ℝ) := by
  have hw : ∀ j ∈ Finset.range (k + 1),
      0 ≤ (Nat.choose k j : ℝ) / (2 : ℝ) ^ k := by
    intro j hj
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hcs := weighted_cauchy_schwarz (Finset.range (k + 1))
    (fun j => (Nat.choose k j : ℝ) / (2 : ℝ) ^ k)
    (fun j => |2 * (j : ℝ) - (k : ℝ)|) hw
  have hsq :
      (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) / (2 : ℝ) ^ k *
          |2 * (j : ℝ) - (k : ℝ)| ^ 2) = (k : ℝ) := by
    rw [show (∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) / (2 : ℝ) ^ k *
          |2 * (j : ℝ) - (k : ℝ)| ^ 2) =
        ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) / (2 : ℝ) ^ k *
            (2 * (j : ℝ) - (k : ℝ)) ^ 2 by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sq_abs]]
    exact inner_second_moment k
  rw [inner_weight_sum k, hsq, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

lemma outer_normalization (n : ℕ) (q : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * q ^ k * (1 - q) ^ (n - k)) = 1 := by
  have h := add_pow q (1 - q) n
  rw [add_sub_cancel] at h
  calc
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * q ^ k * (1 - q) ^ (n - k)) =
        ∑ k ∈ Finset.range (n + 1),
          q ^ k * (1 - q) ^ (n - k) * (Nat.choose n k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 1 := by
      rw [← h]
      exact one_pow n

lemma succ_mul_choose_succ_real (m k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ) =
      ((m + 1 : ℕ) : ℝ) * (Nat.choose m k : ℝ) := by
  have h := Nat.add_one_mul_choose_eq m k
  have h' : ((Nat.choose (m + 1) (k + 1) * (k + 1) : ℕ) : ℝ) =
      (((m + 1) * Nat.choose m k : ℕ) : ℝ) := by
    exact_mod_cast h.symm
  simpa [mul_comm, mul_left_comm, mul_assoc] using h'

lemma outer_first_moment (n : ℕ) (q : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * q ^ k * (1 - q) ^ (n - k) * (k : ℝ)) =
      (n : ℝ) * q := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, add_zero]
      calc
        (∑ k ∈ Finset.range (m + 1),
          (Nat.choose (m + 1) (k + 1) : ℝ) * q ^ (k + 1) *
            (1 - q) ^ (m + 1 - (k + 1)) * ((k + 1 : ℕ) : ℝ)) =
            ∑ k ∈ Finset.range (m + 1),
              (((m + 1 : ℕ) : ℝ) * q) *
                ((Nat.choose m k : ℝ) * q ^ k * (1 - q) ^ (m - k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt : k < m + 1 := Finset.mem_range.mp hk
          have hsub : m + 1 - (k + 1) = m - k := by omega
          rw [hsub]
          calc
            (Nat.choose (m + 1) (k + 1) : ℝ) * q ^ (k + 1) *
                (1 - q) ^ (m - k) * ((k + 1 : ℕ) : ℝ) =
                (((k + 1 : ℕ) : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ)) *
                  (q ^ (k + 1) * (1 - q) ^ (m - k)) := by ring
            _ = (((m + 1 : ℕ) : ℝ) * (Nat.choose m k : ℝ)) *
                  (q ^ (k + 1) * (1 - q) ^ (m - k)) := by
                rw [succ_mul_choose_succ_real m k]
            _ = (((m + 1 : ℕ) : ℝ) * q) *
                  ((Nat.choose m k : ℝ) * q ^ k * (1 - q) ^ (m - k)) := by
                rw [pow_succ]
                ring
        _ = (((m + 1 : ℕ) : ℝ) * q) *
              (∑ k ∈ Finset.range (m + 1),
                (Nat.choose m k : ℝ) * q ^ k * (1 - q) ^ (m - k)) := by
          rw [Finset.mul_sum]
        _ = ((m + 1 : ℕ) : ℝ) * q := by
          rw [outer_normalization]
          ring

theorem binomial_bound (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k) *
        (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) / 2 ^ k * |2 * (j : ℝ) - k|) ≤
      Real.sqrt (n * q) := by
  let w : ℕ → ℝ := fun k => (Nat.choose n k : ℝ) * q ^ k * (1 - q) ^ (n - k)
  have hw_nonneg : ∀ k ∈ Finset.range (n + 1), 0 ≤ w k := by
    intro k hk
    dsimp [w]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 k))
      (pow_nonneg (sub_nonneg.mpr hq1) (n - k))
  have hstep :
      (∑ k ∈ Finset.range (n + 1), w k *
        (∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) / (2 : ℝ) ^ k * |2 * (j : ℝ) - (k : ℝ)|)) ≤
        ∑ k ∈ Finset.range (n + 1), w k * Real.sqrt (k : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (inner_abs_bound k) (hw_nonneg k hk)
  have hnorm : (∑ k ∈ Finset.range (n + 1), w k) = 1 := by
    simpa [w] using outer_normalization n q
  have hmom :
      (∑ k ∈ Finset.range (n + 1), w k * (Real.sqrt (k : ℝ)) ^ 2) =
        (n : ℝ) * q := by
    calc
      (∑ k ∈ Finset.range (n + 1), w k * (Real.sqrt (k : ℝ)) ^ 2) =
          ∑ k ∈ Finset.range (n + 1), w k * (k : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Real.sq_sqrt (Nat.cast_nonneg k)]
      _ = (n : ℝ) * q := by
        simpa [w] using outer_first_moment n q
  have hcs := weighted_cauchy_schwarz (Finset.range (n + 1)) w
    (fun k => Real.sqrt (k : ℝ)) hw_nonneg
  rw [hnorm, hmom, one_mul] at hcs
  exact hstep.trans (Real.le_sqrt_of_sq_le hcs)

end FastCLO.LowerBound

end Prove2SwarmSubmission

theorem solution (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k) *
        (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) / 2 ^ k * |2 * (j : ℝ) - k|) ≤
      Real.sqrt (n * q) := by
  exact Prove2SwarmSubmission.FastCLO.LowerBound.binomial_bound n q hq0 hq1
