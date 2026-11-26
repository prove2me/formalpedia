-- Prove2me | solution 1 for Erdos287.coprime_convolution_reallocate_common_divisors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:03:42.403156+00:00
-- url     : https://prove2.me/submissions/239207a1-da95-48f5-ae5f-6fbeefcd4c3c

import Mathlib

open Finset
open scoped ArithmeticFunction.Moebius

set_option autoImplicit false

private theorem coprime_indicator (r s R S : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hrR : r ≤ R) (hsS : s ≤ S) :
    (∑ d ∈ Icc 1 (min R S), if d ∣ r ∧ d ∣ s then (μ d : ℂ) else 0) =
      if r.Coprime s then 1 else 0 := by
  have hg : (Icc 1 (min R S)).filter (fun d => d ∣ r ∧ d ∣ s) = (r.gcd s).divisors := by
    ext d
    constructor
    · intro hd
      obtain ⟨_, hdr, hds⟩ := mem_filter.mp hd
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdr hds, (Nat.gcd_pos_of_pos_left s hr).ne'⟩
    · intro hd
      have hdg := (Nat.mem_divisors.mp hd).1
      have hdr := hdg.trans (Nat.gcd_dvd_left r s)
      have hds := hdg.trans (Nat.gcd_dvd_right r s)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        le_min ((Nat.le_of_dvd hr hdr).trans hrR) ((Nat.le_of_dvd hs hds).trans hsS)⟩, hdr, hds⟩
  rw [← sum_filter, hg]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (r.gcd s))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, Nat.Coprime] using h

private theorem sum_multiples (N d : ℕ) (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n) = ∑ j ∈ Icc 1 (N / d), f (d * j) := by
  have himage : (Icc 1 (N / d)).image (d * ·) = (Icc 1 N).filter (d ∣ ·) := by
    ext n
    constructor
    · intro hn
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hn
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp hj
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hlo, ?_⟩, dvd_mul_right d j⟩
      simpa only [mul_comm d j] using (Nat.le_div_iff_mul_le hd).mp hhi
    · intro hn
      obtain ⟨hi, j, rfl⟩ := mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp hi
      have hj : 1 ≤ j := by
        by_contra! hj
        have hj0 : j = 0 := by omega
        simp [hj0] at hlo
      refine mem_image.mpr ⟨j, mem_Icc.mpr ⟨hj, (Nat.le_div_iff_mul_le hd).mpr ?_⟩, rfl⟩
      simpa only [mul_comm d j] using hhi
  rw [← himage, sum_image fun _ _ _ _ h => (Nat.mul_left_cancel_iff hd).mp h]

/-- Reallocate the common divisor in a coprime convolution to the first
modulus factor, keeping the product of the two modulus labels unchanged. -/
theorem solution (R S : ℕ) (A B E : ℕ → ℂ) :
    (∑ r ∈ Finset.Icc 1 R, ∑ s ∈ (Finset.Icc 1 S).filter (fun s => r.Coprime s),
      A r * B s * E (r * s)) =
    ∑ d ∈ Finset.Icc 1 (min R S), (ArithmeticFunction.moebius d : ℂ) *
      ∑ u ∈ Finset.Icc 1 (R / d), ∑ v ∈ Finset.Icc 1 (S / d),
        A (d * u) * B (d * v) * E (d * d * u * v) := by
  let T (r s : ℕ) := A r * B s * E (r * s)
  let F (d r s : ℕ) := if d ∣ r ∧ d ∣ s then (μ d : ℂ) * T r s else 0
  let L := Icc 1 R
  let U := Icc 1 S
  let D := Icc 1 (min R S)
  change (∑ r ∈ L, ∑ s ∈ U.filter (fun s => r.Coprime s), T r s) = _
  calc
    _ = ∑ r ∈ L, ∑ s ∈ U, ∑ d ∈ D, F d r s := by
      apply sum_congr rfl
      intro r hr
      rw [sum_filter]
      apply sum_congr rfl
      intro s hs
      obtain ⟨hr0, hrR⟩ := mem_Icc.mp hr
      obtain ⟨hs0, hsS⟩ := mem_Icc.mp hs
      have he := coprime_indicator r s R S hr0 hs0 hrR hsS
      have hT :
          (∑ d ∈ D, (if d ∣ r ∧ d ∣ s then (μ d : ℂ) else 0)) * T r s =
            ∑ d ∈ D, F d r s := by
        rw [sum_mul]
        apply sum_congr rfl
        intro d _
        by_cases h : d ∣ r ∧ d ∣ s <;> simp [F, h]
      rw [← hT, show (∑ d ∈ D, if d ∣ r ∧ d ∣ s then (μ d : ℂ) else 0) =
          if r.Coprime s then 1 else 0 from he]
      split_ifs <;> simp
    _ = ∑ r ∈ L, ∑ d ∈ D, ∑ s ∈ U, F d r s :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ d ∈ D, ∑ r ∈ L, ∑ s ∈ U, F d r s := sum_comm
    _ = ∑ d ∈ D, (μ d : ℂ) *
          ∑ r ∈ L.filter (d ∣ ·), ∑ s ∈ U.filter (d ∣ ·), T r s := by
      apply sum_congr rfl
      intro d _
      simp only [sum_filter, mul_sum]
      apply sum_congr rfl
      intro r _
      by_cases hr : d ∣ r
      · simp only [hr, if_true]
        rw [mul_sum]
        apply sum_congr rfl
        intro s _
        by_cases hs : d ∣ s <;> simp [F, hr, hs]
      · simp [F, hr]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      rw [sum_multiples R d hd0]
      congr 1
      apply sum_congr rfl
      intro u _
      rw [sum_multiples S d hd0]
      apply sum_congr rfl
      intro v _
      simp only [T]
      rw [show (d * u) * (d * v) = d * d * u * v by ring]

