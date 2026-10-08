-- Prove2me | solution 1 for FosterQueues.MG1.theorem7_branching_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:17:27.324556+00:00
-- url     : https://prove2.me/submissions/1bbdefcc-d9ad-47db-9dd0-48731812603a

import Mathlib

open scoped ENNReal

set_option autoImplicit false

namespace P47449922

lemma aux1 (x : ℝ) (h0 : 0 ≤ x) (n : ℕ) : 1 - x ^ n ≤ (n : ℝ) * (1 - x) := by
  have := one_add_mul_sub_le_pow (a := x) (by linarith) n
  linarith

lemma aux2 (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    1 - x ^ (n + 2) < ((n + 2 : ℕ) : ℝ) * (1 - x) := by
  have h := aux1 x h0 (n + 1)
  have hp : x ^ (n + 1) < 1 := pow_lt_one₀ h0 h1 (by omega)
  have e : x ^ (n + 2) = x ^ (n + 1) * x := pow_succ x (n + 1)
  push_cast at h ⊢
  nlinarith

lemma aux3 (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    (n : ℝ) * (1 - x) * x ^ n ≤ 1 - x ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ x ^ k := pow_nonneg h0 k
    have hp1 : x ^ k ≤ 1 := pow_le_one₀ h0 h1
    have e : x ^ (k + 1) = x ^ k * x := pow_succ x k
    rw [e]; push_cast
    nlinarith [mul_nonneg hp (sub_nonneg.2 h1), mul_nonneg (mul_nonneg hp (sub_nonneg.2 h1)) (sub_nonneg.2 h1),
      mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg (mul_nonneg hp (sub_nonneg.2 h1)) (sub_nonneg.2 h1))]

end P47449922

open scoped ENNReal in
theorem solution (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n) (hsum : HasSum q 1)
    (hq0 : 0 < q 0) :
    (∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ ∑' n : ℕ, ξ ^ n * q n = ξ) ↔
      1 < ∑' n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (q n) := by
  have hqs : Summable q := hsum.summable
  have hq1 : ∑' n, q n = 1 := hsum.tsum_eq
  have hGs : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Summable (fun n => s ^ n * q n) := fun s h0 h1 =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg h0 n) (hq n))
      (fun n => mul_le_of_le_one_left (hq n) (pow_le_one₀ h0 h1)) hqs
  have hDs : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Summable (fun n => q n * (1 - s ^ n)) := by
    intro s h0 h1
    have : (fun n => q n * (1 - s ^ n)) = fun n => q n - s ^ n * q n := by funext n; ring
    rw [this]; exact hqs.sub (hGs s h0 h1)
  have hid : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∑' n, q n * (1 - s ^ n) = 1 - ∑' n, s ^ n * q n := by
    intro s h0 h1
    have : (fun n => q n * (1 - s ^ n)) = fun n => q n - s ^ n * q n := by funext n; ring
    rw [this, Summable.tsum_sub hqs (hGs s h0 h1), hq1]
  have hterm : ∀ n : ℕ, (n : ℝ≥0∞) * ENNReal.ofReal (q n) = ENNReal.ofReal ((n : ℝ) * q n) := by
    intro n; rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [hterm]
  constructor
  · rintro ⟨ξ, hξ0, hξ1, hfix⟩
    by_contra hle
    push_neg at hle
    have hne : ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * q n) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hms : Summable (fun n : ℕ => (n : ℝ) * q n) := by
      refine (ENNReal.summable_toReal hne).congr (fun n => ?_)
      exact ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (hq _))
    have hmean : ∑' n : ℕ, (n : ℝ) * q n ≤ 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg _) (hq _)) hms] at hle
      exact ENNReal.ofReal_le_one.1 hle
    obtain ⟨m, hm2, hqm⟩ : ∃ m, 2 ≤ m ∧ 0 < q m := by
      by_contra hno
      push_neg at hno
      have hz : ∀ n, 2 ≤ n → q n = 0 := fun n hn => le_antisymm (hno n hn) (hq n)
      have e1 : ∑' n, q n = ∑ n ∈ Finset.range 2, q n :=
        tsum_eq_sum (fun n hn => hz n (by simp at hn; omega))
      have e2 : ∑' n, ξ ^ n * q n = ∑ n ∈ Finset.range 2, ξ ^ n * q n :=
        tsum_eq_sum (fun n hn => by rw [hz n (by simp at hn; omega), mul_zero])
      rw [hq1] at e1
      rw [hfix] at e2
      simp [Finset.sum_range_succ] at e1 e2
      nlinarith
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have hlt : ∑' n, q n * (1 - ξ ^ n) < ∑' n : ℕ, ((n : ℝ) * q n) * (1 - ξ) := by
      refine Summable.tsum_lt_tsum (i := k + 2) (fun n => ?_) ?_ (hDs ξ hξ0.le hξ1.le)
        (hms.mul_right _)
      · nlinarith [mul_le_mul_of_nonneg_left (P47449922.aux1 ξ hξ0.le n) (hq n)]
      · nlinarith [mul_lt_mul_of_pos_left (P47449922.aux2 ξ hξ0.le hξ1 k) hqm]
    rw [hid ξ hξ0.le hξ1.le, hfix, tsum_mul_right] at hlt
    nlinarith
  · intro hgt
    rw [ENNReal.tsum_eq_iSup_nat] at hgt
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 hgt
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _) (hq _)),
      ENNReal.one_lt_ofReal] at hN
    set A := ∑ n ∈ Finset.range N, (n : ℝ) * q n with hA
    have hev : ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Iio 1), 0 < s ∧ 1 < s ^ N * A := by
      have h1 : ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Iio 1), 0 < s := by
        filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with s hs using hs.1
      have ht : Filter.Tendsto (fun s : ℝ => s ^ N * A) (nhdsWithin (1:ℝ) (Set.Iio 1))
          (nhds ((1:ℝ) ^ N * A)) :=
        (((continuous_pow N).mul continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
      have h2 : ∀ᶠ s in nhdsWithin (1:ℝ) (Set.Iio 1), 1 < s ^ N * A :=
        ht.eventually (lt_mem_nhds (by simpa using hN))
      exact h1.and h2
    obtain ⟨s, ⟨hs0, hsA⟩, hs1⟩ := (hev.and self_mem_nhdsWithin).exists
    have hs1' : s < 1 := hs1
    have key : 1 - s < ∑' n, q n * (1 - s ^ n) := by
      calc 1 - s < (1 - s) * (s ^ N * A) := by nlinarith
        _ = ∑ n ∈ Finset.range N, (1 - s) * (s ^ N * ((n : ℝ) * q n)) := by
          rw [hA, Finset.mul_sum, Finset.mul_sum]
        _ ≤ ∑ n ∈ Finset.range N, q n * (1 - s ^ n) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hnN : n ≤ N := (Finset.mem_range.1 hn).le
          have hp : s ^ N ≤ s ^ n := pow_le_pow_of_le_one hs0.le hs1'.le hnN
          have c1 := mul_le_mul_of_nonneg_left hp
            (mul_nonneg (hq n) (mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sub_nonneg.2 hs1'.le)))
          have c2 := mul_le_mul_of_nonneg_left (P47449922.aux3 s hs0.le hs1'.le n) (hq n)
          nlinarith
        _ ≤ ∑' n, q n * (1 - s ^ n) :=
          (hDs s hs0.le hs1'.le).sum_le_tsum _ (fun n _ => mul_nonneg (hq n)
            (sub_nonneg.2 (pow_le_one₀ hs0.le hs1'.le)))
    rw [hid s hs0.le hs1'.le] at key
    have hcont : ContinuousOn (fun x : ℝ => ∑' n, x ^ n * q n - x) (Set.Icc 0 s) := by
      refine (continuousOn_tsum (f := fun n (x : ℝ) => x ^ n * q n) (fun n => ((continuous_pow n).mul continuous_const).continuousOn)
        hqs (fun n x hx => ?_)).sub continuousOn_id
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.1 n) (hq n))]
      exact mul_le_of_le_one_left (hq n) (pow_le_one₀ hx.1 (hx.2.trans hs1'.le))
    have hG0 : ∑' n, (0:ℝ) ^ n * q n = q 0 := by
      rw [tsum_eq_single 0 (fun n hn => by simp [hn])]; simp
    obtain ⟨ξ, hξ, hξeq⟩ := intermediate_value_Icc' hs0.le hcont
      (show (0:ℝ) ∈ Set.Icc (∑' n, s ^ n * q n - s) (∑' n, (0:ℝ) ^ n * q n - 0) from
        ⟨by linarith, by rw [hG0]; linarith⟩)
    simp only at hξeq
    refine ⟨ξ, ?_, by linarith [hξ.2], by linarith⟩
    rcases hξ.1.lt_or_eq with h | h
    · exact h
    · subst h; rw [hG0] at hξeq; linarith
