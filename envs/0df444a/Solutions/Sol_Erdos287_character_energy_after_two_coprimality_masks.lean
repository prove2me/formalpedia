-- Prove2me | solution 1 for Erdos287.character_energy_after_two_coprimality_masks
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:40:14.874098+00:00
-- url     : https://prove2.me/submissions/1a466117-1117-408f-8a93-1187f6fa7aad

import Mathlib

open Finset
open scoped ArithmeticFunction.Moebius

set_option autoImplicit false

private theorem moebius_coprime_mask (m n : ℕ) (hm : 0 < m) :
    (∑ d ∈ m.divisors.filter (· ∣ n), (μ d : ℂ)) =
      if n.Coprime m then 1 else 0 := by
  have hg : m.divisors.filter (· ∣ n) = (m.gcd n).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hm0 := hm.ne'
    have hg0 := (Nat.gcd_pos_of_pos_left n hm).ne'
    tauto
  rw [hg]
  have h := congrArg (fun f : ArithmeticFunction ℂ => f (m.gcd n))
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply, Nat.gcd_comm m n, Nat.Coprime] using h

private theorem sum_multiples (N d : ℕ) (hd : 0 < d) (f : ℕ → ℂ) :
    (∑ n ∈ (Icc 1 N).filter (d ∣ ·), f n) = ∑ j ∈ Icc 1 (N / d), f (d * j) := by
  let J := Icc 1 (N / d)
  have himage : J.image (d * ·) = (Icc 1 N).filter (d ∣ ·) := by
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

private theorem one_mask (N m : ℕ) (hm : 0 < m) (A χ : ℕ → ℂ)
    (hmul : ∀ d n, χ (d * n) = χ d * χ n) (hnorm : ∀ n, ‖χ n‖ ≤ 1) :
    ‖∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime m), A n * χ n‖ ^ 2 ≤
      (m.divisors.card : ℝ) * ∑ d ∈ m.divisors, ‖∑ j ∈ Icc 1 (N / d), A (d * j) * χ j‖ ^ 2 := by
  let S := Icc 1 N
  let Z (d : ℕ) := ∑ j ∈ Icc 1 (N / d), A (d * j) * χ j
  have hexpand :
      (∑ n ∈ S.filter (fun n => n.Coprime m), A n * χ n) =
        ∑ d ∈ m.divisors, ((μ d : ℂ) * χ d) * Z d := by
    calc
      _ = ∑ n ∈ S, (∑ d ∈ m.divisors.filter (· ∣ n), (μ d : ℂ)) * (A n * χ n) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        rw [moebius_coprime_mask m n hm]
        split_ifs <;> simp
      _ = ∑ d ∈ m.divisors, ∑ n ∈ S.filter (d ∣ ·), (μ d : ℂ) * (A n * χ n) := by
        simp only [sum_filter, sum_mul]
        rw [sum_comm]
        apply sum_congr rfl
        intro d _
        apply sum_congr rfl
        intro n _
        split_ifs <;> simp
      _ = _ := by
        apply sum_congr rfl
        intro d hd
        rw [sum_multiples N d (Nat.pos_of_mem_divisors hd)]
        simp only [Z, mul_sum, hmul]
        apply sum_congr rfl
        intro j _
        ring
  have hpoint (d : ℕ) : ‖((μ d : ℂ) * χ d) * Z d‖ ≤ ‖Z d‖ := by
    have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> simp [h]
    rw [norm_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ hμ (norm_nonneg _) (hnorm d))
  rw [hexpand]
  have htriangle : ‖∑ d ∈ m.divisors, ((μ d : ℂ) * χ d) * Z d‖ ≤
      ∑ d ∈ m.divisors, ‖Z d‖ :=
    (norm_sum_le _ _).trans (sum_le_sum fun d _ => hpoint d)
  exact (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans (by
    simpa using sum_mul_sq_le_sq_mul_sq m.divisors (fun _ => (1 : ℝ)) (fun d => ‖Z d‖))

/-- Two coprimality masks in a character sum can be removed at the cost of two
divisor sums, while retaining the shortened length in each summand. -/
theorem solution (N a b : ℕ) (ha : 0 < a) (hb : 0 < b) (A χ : ℕ → ℂ)
    (hmul : ∀ d n, χ (d * n) = χ d * χ n) (hnorm : ∀ n, ‖χ n‖ ≤ 1) :
    ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Coprime (a * b)), A n * χ n‖ ^ 2 ≤
      ((a.divisors.card : ℝ) * b.divisors.card) *
        ∑ d ∈ a.divisors, ∑ v ∈ b.divisors,
          ‖∑ j ∈ Finset.Icc 1 (N / (d * v)), A (d * v * j) * χ j‖ ^ 2 := by
  let F (n : ℕ) := if n.Coprime b then A n else 0
  have hsplit : (∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime (a * b)), A n * χ n) =
      ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime a), F n * χ n := by
    simp only [sum_filter]
    apply sum_congr rfl
    intro n _
    by_cases hna : n.Coprime a
    · by_cases hnb : n.Coprime b
      · have hab := Nat.coprime_mul_iff_right.mpr ⟨hna, hnb⟩
        simp only [if_pos hab, if_pos hna, F, if_pos hnb]
      · have hab : ¬ n.Coprime (a * b) :=
          fun h => hnb (Nat.coprime_mul_iff_right.mp h).2
        simp only [if_neg hab, if_pos hna, F, if_neg hnb, zero_mul]
    · have hab : ¬ n.Coprime (a * b) :=
        fun h => hna (Nat.coprime_mul_iff_right.mp h).1
      simp only [if_neg hab, if_neg hna]
  rw [hsplit]
  refine (one_mask N a ha F χ hmul hnorm).trans ?_
  let Z (d : ℕ) := ∑ v ∈ b.divisors, ‖∑ j ∈ Icc 1 (N / (d * v)), A (d * v * j) * χ j‖ ^ 2
  change (a.divisors.card : ℝ) *
    (∑ d ∈ a.divisors, ‖∑ j ∈ Icc 1 (N / d), F (d * j) * χ j‖ ^ 2) ≤
      _ * ∑ d ∈ a.divisors, Z d
  rw [mul_assoc, mul_sum a.divisors Z (b.divisors.card : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro d _
  by_cases hd : d.Coprime b
  · have hrestrict :
        (∑ j ∈ Icc 1 (N / d), F (d * j) * χ j) =
          ∑ j ∈ (Icc 1 (N / d)).filter (fun j => j.Coprime b), A (d * j) * χ j := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      by_cases hj : j.Coprime b
      · have hdj := Nat.coprime_mul_iff_left.mpr ⟨hd, hj⟩
        simp only [F, if_pos hdj, if_pos hj]
      · have hdj : ¬ (d * j).Coprime b :=
          fun h => hj (Nat.coprime_mul_iff_left.mp h).2
        simp only [F, if_neg hdj, if_neg hj, zero_mul]
    rw [hrestrict]
    simpa only [Z, Nat.div_div_eq_div_mul, mul_assoc] using
      one_mask (N / d) b hb (fun n => A (d * n)) χ hmul hnorm
  · have hzero (j : ℕ) : F (d * j) = 0 := by
      have hdj : ¬ (d * j).Coprime b :=
        fun h => hd (Nat.coprime_mul_iff_left.mp h).1
      exact if_neg hdj
    simp only [hzero, zero_mul, sum_const_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)

