-- Prove2me | solution 1 for BanditAlgorithm.asymptotic_ucb_schedule_reciprocal_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T15:26:01.994185+00:00
-- url     : https://prove2.me/submissions/3fb16fe8-e5bd-41d1-84a5-04028995c395

import Definitions.Def_asymptoticUcbPolicy
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators
open Set

namespace BanditAlgorithm

lemma log_two_lower : (693 : ℝ) / 1000 ≤ Real.log 2 := by
  have hs := Real.hasSum_log_one_add_inv (a := (1 : ℝ)) one_pos
  have hle := hs.summable.sum_le_tsum (Finset.range 3) (fun i hi ↦ by
    positivity)
  rw [hs.tsum_eq] at hle
  norm_num [Finset.sum_range_succ] at hle ⊢
  linarith

lemma log_nat_lower_of_pow_two {p t : ℕ} (hpt : 2 ^ p ≤ t) :
    (p : ℝ) * (693 / 1000 : ℝ) +
        2 * ((t : ℝ) - (2 ^ p : ℕ)) / ((t : ℝ) + (2 ^ p : ℕ)) ≤
      Real.log t := by
  have hqnat : 0 < 2 ^ p := pow_pos (by omega : 0 < (2 : ℕ)) _
  have htnat : 0 < t := lt_of_lt_of_le hqnat hpt
  have hq : (0 : ℝ) < (2 ^ p : ℕ) := by exact_mod_cast hqnat
  have ht : (0 : ℝ) < t := by exact_mod_cast htnat
  have hratio : (1 : ℝ) ≤ (t : ℝ) / (2 ^ p : ℕ) := by
    rw [le_div_iff₀ hq]
    norm_num
    exact_mod_cast hpt
  have hx : 0 ≤ (t : ℝ) / (2 ^ p : ℕ) - 1 := sub_nonneg.mpr hratio
  have hlog_ratio := Real.le_log_one_add_of_nonneg hx
  have hlog_pow :
      (p : ℝ) * (693 / 1000 : ℝ) ≤ Real.log ((2 : ℝ) ^ p) := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left log_two_lower (Nat.cast_nonneg p)
  have hratio_form :
      2 * ((t : ℝ) / (2 ^ p : ℕ) - 1) /
          (((t : ℝ) / (2 ^ p : ℕ) - 1) + 2) =
        2 * ((t : ℝ) - (2 ^ p : ℕ)) /
          ((t : ℝ) + (2 ^ p : ℕ)) := by
    have hnum :
        (t : ℝ) / (2 ^ p : ℕ) - 1 =
          ((t : ℝ) - (2 ^ p : ℕ)) / (2 ^ p : ℕ) := by
      field_simp [ne_of_gt hq]
    have hden :
        (t : ℝ) / (2 ^ p : ℕ) - 1 + 2 =
          ((t : ℝ) + (2 ^ p : ℕ)) / (2 ^ p : ℕ) := by
      field_simp [ne_of_gt hq]
      ring
    rw [hden, hnum]
    field_simp [ne_of_gt hq, ne_of_gt (add_pos ht hq)]
  have hlog_ratio' :
        2 * ((t : ℝ) - (2 ^ p : ℕ)) /
          ((t : ℝ) + (2 ^ p : ℕ)) ≤
        Real.log ((t : ℝ) / (2 ^ p : ℕ)) := by
    rw [hratio_form] at hlog_ratio
    convert hlog_ratio using 1
    congr 2
    ring
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hq)] at hlog_ratio'
  have hcastpow : ((2 ^ p : ℕ) : ℝ) = (2 : ℝ) ^ p := by norm_num
  rw [← hcastpow] at hlog_pow
  linarith

lemma schedule_reciprocal_le_of_log_lower
    (t : ℕ) {L B : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ Real.log t)
    (hB : 1 / (1 + (t : ℝ) * L ^ 2) ≤ B) :
    1 / asymptoticUcbSchedule t ≤ B := by
  have hlog0 : 0 ≤ Real.log t := hL0.trans hL
  have hsq : L ^ 2 ≤ Real.log t ^ 2 := by nlinarith
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hden :
      1 + (t : ℝ) * L ^ 2 ≤ asymptoticUcbSchedule t := by
    simp only [asymptoticUcbSchedule]
    nlinarith
  have hden0 : 0 < 1 + (t : ℝ) * L ^ 2 := by positivity
  exact (one_div_le_one_div_of_le hden0 hden).trans hB

lemma schedule_reciprocal_head_bound :
    ∑ t ∈ Finset.Icc 1 19, 1 / asymptoticUcbSchedule t ≤
      (43179 : ℝ) / 20000 := by
  have h2 : (693 : ℝ) / 1000 ≤ Real.log 2 := log_two_lower
  have h3 : (1093 : ℝ) / 1000 ≤ Real.log 3 := by
    have h := log_nat_lower_of_pow_two (p := 1) (t := 3) (by norm_num)
    norm_num at h ⊢
    exact h
  have h4 : (693 : ℝ) / 500 ≤ Real.log 4 := by
    have h := log_nat_lower_of_pow_two (p := 2) (t := 4) (by norm_num)
    norm_num at h ⊢
    exact h
  have h5 : (7237 : ℝ) / 4500 ≤ Real.log 5 := by
    have h := log_nat_lower_of_pow_two (p := 2) (t := 5) (by norm_num)
    norm_num at h ⊢
    exact h
  have h6 : (893 : ℝ) / 500 ≤ Real.log 6 := by
    have h := log_nat_lower_of_pow_two (p := 2) (t := 6) (by norm_num)
    norm_num at h ⊢
    exact h
  have h7 : (10623 : ℝ) / 5500 ≤ Real.log 7 := by
    have h := log_nat_lower_of_pow_two (p := 2) (t := 7) (by norm_num)
    norm_num at h ⊢
    exact h
  have h8 : (2079 : ℝ) / 1000 ≤ Real.log 8 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 8) (by norm_num)
    norm_num at h ⊢
    exact h
  have h9 : (37343 : ℝ) / 17000 ≤ Real.log 9 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 9) (by norm_num)
    norm_num at h ⊢
    exact h
  have h10 : (20711 : ℝ) / 9000 ≤ Real.log 10 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 10) (by norm_num)
    norm_num at h ⊢
    exact h
  have h11 : (45501 : ℝ) / 19000 ≤ Real.log 11 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 11) (by norm_num)
    norm_num at h ⊢
    exact h
  have h12 : (2479 : ℝ) / 1000 ≤ Real.log 12 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 12) (by norm_num)
    norm_num at h ⊢
    exact h
  have h13 : (53659 : ℝ) / 21000 ≤ Real.log 13 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 13) (by norm_num)
    norm_num at h ⊢
    exact h
  have h14 : (28869 : ℝ) / 11000 ≤ Real.log 14 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 14) (by norm_num)
    norm_num at h ⊢
    exact h
  have h15 : (61817 : ℝ) / 23000 ≤ Real.log 15 := by
    have h := log_nat_lower_of_pow_two (p := 3) (t := 15) (by norm_num)
    norm_num at h ⊢
    exact h
  have h16 : (693 : ℝ) / 250 ≤ Real.log 16 := by
    have h := log_nat_lower_of_pow_two (p := 4) (t := 16) (by norm_num)
    norm_num at h ⊢
    exact h
  have h17 : (23369 : ℝ) / 8250 ≤ Real.log 17 := by
    have h := log_nat_lower_of_pow_two (p := 4) (t := 17) (by norm_num)
    norm_num at h ⊢
    exact h
  have h18 : (12281 : ℝ) / 4250 ≤ Real.log 18 := by
    have h := log_nat_lower_of_pow_two (p := 4) (t := 18) (by norm_num)
    norm_num at h ⊢
    exact h
  have h19 : (5151 : ℝ) / 1750 ≤ Real.log 19 := by
    have h := log_nat_lower_of_pow_two (p := 4) (t := 19) (by norm_num)
    norm_num at h ⊢
    exact h
  let B : ℕ → ℝ
    | 1 => 1
    | 2 => 1594 / 3125
    | 3 => 2727 / 12500
    | 4 => 2879 / 25000
    | 5 => 3589 / 50000
    | 6 => 2483 / 50000
    | 7 => 3689 / 100000
    | 8 => 2811 / 100000
    | 9 => 2251 / 100000
    | 10 => 927 / 50000
    | 11 => 1561 / 100000
    | 12 => 669 / 50000
    | 13 => 233 / 20000
    | 14 => 1027 / 100000
    | 15 => 183 / 20000
    | 16 => 807 / 100000
    | 17 => 91 / 12500
    | 18 => 661 / 100000
    | 19 => 151 / 25000
    | _ => 0
  have hterm :
      ∀ t ∈ Finset.Icc 1 19, 1 / asymptoticUcbSchedule t ≤ B t := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    rcases ht with ⟨ht1, ht19⟩
    interval_cases t
    · exact schedule_reciprocal_le_of_log_lower 1
        (L := 0) (B := B 1) (by norm_num) (by norm_num)
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 2
        (L := 693 / 1000) (B := B 2) (by norm_num) h2
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 3
        (L := 1093 / 1000) (B := B 3) (by norm_num) h3
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 4
        (L := 693 / 500) (B := B 4) (by norm_num) h4
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 5
        (L := 7237 / 4500) (B := B 5) (by norm_num) h5
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 6
        (L := 893 / 500) (B := B 6) (by norm_num) h6
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 7
        (L := 10623 / 5500) (B := B 7) (by norm_num) h7
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 8
        (L := 2079 / 1000) (B := B 8) (by norm_num) h8
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 9
        (L := 37343 / 17000) (B := B 9) (by norm_num) h9
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 10
        (L := 20711 / 9000) (B := B 10) (by norm_num) h10
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 11
        (L := 45501 / 19000) (B := B 11) (by norm_num) h11
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 12
        (L := 2479 / 1000) (B := B 12) (by norm_num) h12
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 13
        (L := 53659 / 21000) (B := B 13) (by norm_num) h13
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 14
        (L := 28869 / 11000) (B := B 14) (by norm_num) h14
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 15
        (L := 61817 / 23000) (B := B 15) (by norm_num) h15
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 16
        (L := 693 / 250) (B := B 16) (by norm_num) h16
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 17
        (L := 23369 / 8250) (B := B 17) (by norm_num) h17
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 18
        (L := 12281 / 4250) (B := B 18) (by norm_num) h18
        (by norm_num [B])
    · exact schedule_reciprocal_le_of_log_lower 19
        (L := 5151 / 1750) (B := B 19) (by norm_num) h19
        (by norm_num [B])
  calc
    ∑ t ∈ Finset.Icc 1 19, 1 / asymptoticUcbSchedule t ≤
        ∑ t ∈ Finset.Icc 1 19, B t := Finset.sum_le_sum hterm
    _ = (43179 : ℝ) / 20000 := by norm_num [B, Finset.sum_Icc_succ_top]

lemma reciprocal_log_square_antitone_on {a b : ℝ} (ha : 1 < a) :
    AntitoneOn (fun x : ℝ ↦ 1 / (x * Real.log x ^ 2)) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := lt_trans (by norm_num) (ha.trans_le hx.1)
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlogx : 0 < Real.log x := Real.log_pos (ha.trans_le hx.1)
  have hlogy : 0 < Real.log y :=
    Real.log_pos (lt_of_lt_of_le (ha.trans_le hx.1) hxy)
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxpos hypos hxy
  have hsq : Real.log x ^ 2 ≤ Real.log y ^ 2 := by nlinarith
  have hprod : x * Real.log x ^ 2 ≤ y * Real.log y ^ 2 :=
    mul_le_mul hxy hsq (sq_nonneg _) hypos.le
  exact one_div_le_one_div_of_le (mul_pos hxpos (sq_pos_of_pos hlogx)) hprod

lemma reciprocal_log_square_integral_eq {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ x in a..b, 1 / (x * Real.log x ^ 2) =
      1 / Real.log a - 1 / Real.log b := by
  have hderiv :
      ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ ↦ -(1 / Real.log y))
          (1 / (x * Real.log x ^ 2)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < x := lt_trans (by norm_num) (ha.trans_le hx.1)
    have hlogpos : 0 < Real.log x := Real.log_pos (ha.trans_le hx.1)
    have hd := ((Real.hasDerivAt_log (ne_of_gt hxpos)).inv
      (ne_of_gt hlogpos)).neg
    have hfun :
        (fun y : ℝ ↦ -(1 / Real.log y)) =
          (fun y : ℝ ↦ -(Real.log y)⁻¹) := by
      funext y
      simp only [one_div]
    rw [hfun]
    refine hd.congr_deriv ?_
    field_simp
  have hcont :
      ContinuousOn (fun x : ℝ ↦ 1 / (x * Real.log x ^ 2)) (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hxpos : 0 < x := lt_trans (by norm_num) (ha.trans_le hx.1)
    have hlogpos : 0 < Real.log x := Real.log_pos (ha.trans_le hx.1)
    exact (continuousAt_const.div
      (continuousAt_id.mul ((Real.continuousAt_log (ne_of_gt hxpos)).pow 2))
      (mul_ne_zero (ne_of_gt hxpos) (pow_ne_zero 2 (ne_of_gt hlogpos)))).continuousWithinAt
  have hint :
      IntervalIntegrable (fun x : ℝ ↦ 1 / (x * Real.log x ^ 2))
        MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have hfund :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa only [neg_sub_neg, neg_div, one_div] using hfund

lemma schedule_reciprocal_tail_bound (n : ℕ) :
    ∑ t ∈ Finset.Icc 20 n, 1 / asymptoticUcbSchedule t ≤
      (34 : ℝ) / 100 := by
  by_cases hn : 20 ≤ n
  · have hn19 : 19 ≤ n := by omega
    have hlog19 : (5151 : ℝ) / 1750 ≤ Real.log 19 := by
      have h := log_nat_lower_of_pow_two (p := 4) (t := 19) (by norm_num)
      norm_num at h ⊢
      exact h
    have hlog19pos : 0 < Real.log 19 := (by norm_num : (0 : ℝ) <
        5151 / 1750).trans_le hlog19
    have hterm :
        ∀ t ∈ Finset.Icc 20 n,
          1 / asymptoticUcbSchedule t ≤
            1 / ((t : ℝ) * Real.log t ^ 2) := by
      intro t ht
      simp only [Finset.mem_Icc] at ht
      have htpos : (0 : ℝ) < t := by
        exact_mod_cast (show 0 < t by omega)
      have hlogpos : 0 < Real.log t := by
        apply Real.log_pos
        exact_mod_cast (show 1 < t by omega)
      have hdenpos : 0 < (t : ℝ) * Real.log t ^ 2 :=
        mul_pos htpos (sq_pos_of_pos hlogpos)
      apply one_div_le_one_div_of_le hdenpos
      simp only [asymptoticUcbSchedule]
      linarith
    have hshift :
        (∑ t ∈ Finset.Icc 20 n, 1 / ((t : ℝ) * Real.log t ^ 2)) =
          ∑ i ∈ Finset.Ico 19 n,
            1 / (((i + 1 : ℕ) : ℝ) * Real.log (i + 1 : ℕ) ^ 2) := by
      rw [Finset.sum_Ico_add'
        (fun t : ℕ ↦ 1 / ((t : ℝ) * Real.log t ^ 2)) 19 n 1]
      apply Finset.sum_congr
      · ext t
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro t ht
        rfl
    have hanti :
        AntitoneOn (fun x : ℝ ↦ 1 / (x * Real.log x ^ 2))
          (Set.Icc (19 : ℝ) n) :=
      reciprocal_log_square_antitone_on (by norm_num)
    have hsum_integral :
        (∑ t ∈ Finset.Icc 20 n, 1 / ((t : ℝ) * Real.log t ^ 2)) ≤
          ∫ x in (19 : ℝ)..n, 1 / (x * Real.log x ^ 2) := by
      rw [hshift]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        AntitoneOn.sum_le_integral_Ico hn19 hanti
    have hintegral :
        (∫ x in (19 : ℝ)..n, 1 / (x * Real.log x ^ 2)) =
          1 / Real.log 19 - 1 / Real.log n :=
      reciprocal_log_square_integral_eq (by norm_num) (by exact_mod_cast hn19)
    have hlognpos : 0 < Real.log n := by
      apply Real.log_pos
      exact_mod_cast (show 1 < n by omega)
    have htail :
        (∫ x in (19 : ℝ)..n, 1 / (x * Real.log x ^ 2)) ≤
          1 / Real.log 19 := by
      rw [hintegral]
      have hrecipn : 0 ≤ 1 / Real.log n := one_div_nonneg.mpr hlognpos.le
      linarith
    have hrecip19 : 1 / Real.log 19 ≤ (34 : ℝ) / 100 := by
      apply (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) <
        (5151 : ℝ) / 1750) hlog19).trans
      norm_num
    calc
      ∑ t ∈ Finset.Icc 20 n, 1 / asymptoticUcbSchedule t ≤
          ∑ t ∈ Finset.Icc 20 n,
            1 / ((t : ℝ) * Real.log t ^ 2) :=
        Finset.sum_le_sum hterm
      _ ≤ ∫ x in (19 : ℝ)..n, 1 / (x * Real.log x ^ 2) :=
        hsum_integral
      _ ≤ 1 / Real.log 19 := htail
      _ ≤ (34 : ℝ) / 100 := hrecip19
  · have hempty : Finset.Icc 20 n = ∅ := by
      ext t
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]
      omega
    rw [hempty]
    norm_num

/-- The summability estimate assigned as Exercise 8.1 in Lattimore--Szepesvári,
*Bandit Algorithms*, printed p. 117. -/
theorem asymptotic_ucb_schedule_reciprocal_sum_bound_proof (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, 1 / asymptoticUcbSchedule t ≤ 5 / 2 := by
  by_cases hn : 20 ≤ n
  · have hdisj : Disjoint (Finset.Icc 1 19) (Finset.Icc 20 n) := by
      rw [Finset.disjoint_left]
      intro t ht_head ht_tail
      simp only [Finset.mem_Icc] at ht_head ht_tail
      omega
    have hsplit :
        Finset.Icc 1 n = Finset.Icc 1 19 ∪ Finset.Icc 20 n := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hhead := schedule_reciprocal_head_bound
    have htail := schedule_reciprocal_tail_bound n
    norm_num at hhead htail ⊢
    linarith
  · have hn19 : n ≤ 19 := by omega
    have hsubset : Finset.Icc 1 n ⊆ Finset.Icc 1 19 := by
      intro t ht
      simp only [Finset.mem_Icc] at ht ⊢
      omega
    have hle :
        (∑ t ∈ Finset.Icc 1 n, 1 / asymptoticUcbSchedule t) ≤
          ∑ t ∈ Finset.Icc 1 19, 1 / asymptoticUcbSchedule t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro t ht hnot
        have hpos : 0 < asymptoticUcbSchedule t := by
          simp only [asymptoticUcbSchedule]
          positivity
        exact (one_div_pos.mpr hpos).le)
    exact hle.trans (schedule_reciprocal_head_bound.trans (by norm_num))

end BanditAlgorithm

theorem solution (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n,
        1 / BanditAlgorithm.asymptoticUcbSchedule t ≤ 5 / 2 :=
  BanditAlgorithm.asymptotic_ucb_schedule_reciprocal_sum_bound_proof n
