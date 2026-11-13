-- Prove2me | solution 1 for ConstOverheadCompile.Main.binomial_tail_eq16
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T14:06:14.264239+00:00
-- url     : https://prove2.me/submissions/933d8be1-15a0-4abe-811b-1877258790c9

import Mathlib

set_option autoImplicit false

/-- Chernoff bound for a binomial tail: if `4G ≤ m` then `2^{-m} ∑_{k<G} C(m,k) ≤ e^{-m/8}`.
The proof uses the exponential moment with ratio `3`. -/
theorem solution (G m : ℕ) (h : 4 * G ≤ m) :
    (∑ k ∈ Finset.range G, (m.choose k : ℝ)) / 2 ^ m ≤ Real.exp (-(m : ℝ) / 8) := by
  classical
  set T : ℝ := Real.log 3 with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]
    exact Real.log_pos (by norm_num)
  have hexpT : Real.exp T = 3 := by
    rw [hTdef, Real.exp_log (by norm_num)]
  have hexpnegT : Real.exp (-T) = 1 / 3 := by
    rw [Real.exp_neg, hexpT]
    norm_num
  have hS : (∑ k ∈ Finset.range G, (m.choose k : ℝ)) ≤
      Real.exp (T * (G : ℝ)) * (1 + Real.exp (-T)) ^ m := by
    have hterm : ∀ k ∈ Finset.range G,
        (m.choose k : ℝ) ≤ (m.choose k : ℝ) * Real.exp (T * ((G : ℝ) - (k : ℝ))) := by
      intro k hk
      have hkG : k < G := Finset.mem_range.mp hk
      have hnonneg : (0 : ℝ) ≤ (G : ℝ) - (k : ℝ) := by
        have hkGle : k ≤ G := by omega
        have hcast : (k : ℝ) ≤ (G : ℝ) := by exact_mod_cast hkGle
        linarith
      have hexp1 : 1 ≤ Real.exp (T * ((G : ℝ) - (k : ℝ))) :=
        Real.one_le_exp (mul_nonneg hTpos.le hnonneg)
      exact le_mul_of_one_le_right (Nat.cast_nonneg _) hexp1
    have hsub : Finset.range G ⊆ Finset.range (m + 1) := by
      intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    have hnonneg2 : ∀ k ∈ Finset.range (m + 1), k ∉ Finset.range G →
        0 ≤ (m.choose k : ℝ) * Real.exp (T * ((G : ℝ) - (k : ℝ))) := by
      intro k _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
    have hle1 : (∑ k ∈ Finset.range G, (m.choose k : ℝ)) ≤
        ∑ k ∈ Finset.range G, (m.choose k : ℝ) * Real.exp (T * ((G : ℝ) - (k : ℝ))) :=
      Finset.sum_le_sum hterm
    have hle2 := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg2
    calc (∑ k ∈ Finset.range G, (m.choose k : ℝ))
        ≤ ∑ k ∈ Finset.range G,
            (m.choose k : ℝ) * Real.exp (T * ((G : ℝ) - (k : ℝ))) := hle1
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            (m.choose k : ℝ) * Real.exp (T * ((G : ℝ) - (k : ℝ))) := hle2
      _ = Real.exp (T * (G : ℝ)) * (1 + Real.exp (-T)) ^ m := by
          have hterm2 : ∀ k ∈ Finset.range (m + 1),
              (m.choose k : ℝ) * Real.exp (T * ((G : ℝ) - (k : ℝ))) =
                Real.exp (T * (G : ℝ)) * ((m.choose k : ℝ) * (Real.exp (-T)) ^ k) := by
            intro k hk
            have hexp : Real.exp (T * ((G : ℝ) - (k : ℝ))) =
                Real.exp (T * (G : ℝ)) * (Real.exp (-T)) ^ k := by
              rw [show T * ((G : ℝ) - (k : ℝ)) = T * (G : ℝ) + ((k : ℝ) * (-T)) by ring]
              rw [Real.exp_add, Real.exp_nat_mul]
            rw [hexp]
            ring
          rw [Finset.sum_congr rfl hterm2]
          rw [← Finset.mul_sum]
          congr 1
          rw [show (1 + Real.exp (-T)) = (Real.exp (-T) + 1) by ring]
          rw [add_pow (Real.exp (-T)) 1 m]
          apply Finset.sum_congr rfl
          intro k hk
          simp [mul_comm, mul_left_comm, mul_assoc]
  have hS2 : (∑ k ∈ Finset.range G, (m.choose k : ℝ)) ≤ (3 : ℝ) ^ G * (4 / 3) ^ m := by
    have hexpTG : Real.exp (T * (G : ℝ)) = (3 : ℝ) ^ G := by
      rw [mul_comm, Real.exp_nat_mul, hexpT]
    calc (∑ k ∈ Finset.range G, (m.choose k : ℝ))
        ≤ Real.exp (T * (G : ℝ)) * (1 + Real.exp (-T)) ^ m := hS
      _ = (3 : ℝ) ^ G * (4 / 3) ^ m := by
          rw [hexpTG, hexpnegT]
          norm_num
  have hdiv : (∑ k ∈ Finset.range G, (m.choose k : ℝ)) / 2 ^ m ≤
      (3 : ℝ) ^ G * (2 / 3) ^ m := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)]
    have hmul : (3 : ℝ) ^ G * (2 / 3) ^ m * 2 ^ m = (3 : ℝ) ^ G * (4 / 3) ^ m := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    rw [hmul]
    exact hS2
  have h8main : ((3 : ℝ) ^ G * (2 / 3) ^ m) ^ 8 ≤ (Real.exp (-(m : ℝ) / 8)) ^ 8 := by
    have hLHS : ((3 : ℝ) ^ G * (2 / 3) ^ m) ^ 8 = (3 : ℝ) ^ (8 * G) * ((2 / 3) ^ 8) ^ m := by
      rw [mul_pow]
      congr 1
      · rw [← pow_mul, show G * 8 = 8 * G by ring]
      · rw [← pow_mul, show m * 8 = 8 * m by ring, pow_mul]
    rw [hLHS]
    have hRHS : (Real.exp (-(m : ℝ) / 8)) ^ 8 = (Real.exp (-1)) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [hRHS]
    have h8G : (3 : ℝ) ^ (8 * G) ≤ (3 : ℝ) ^ (2 * m) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega : 8 * G ≤ 2 * m)
    have hstep1 : (3 : ℝ) ^ (8 * G) * ((2 / 3) ^ 8) ^ m ≤
        (3 : ℝ) ^ (2 * m) * ((2 / 3) ^ 8) ^ m :=
      mul_le_mul_of_nonneg_right h8G (by positivity)
    have hcollapse : (3 : ℝ) ^ (2 * m) * ((2 / 3) ^ 8) ^ m = ((256 : ℝ) / 729) ^ m := by
      rw [pow_mul]
      rw [← mul_pow]
      norm_num
    have hbase : (256 : ℝ) / 729 ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      rw [le_div_iff₀ (Real.exp_pos 1)]
      have hlt : (256 : ℝ) / 729 * Real.exp 1 < 1 := by
        have h1 : (256 : ℝ) / 729 * Real.exp 1 < (256 : ℝ) / 729 * 2.7182818286 :=
          mul_lt_mul_of_pos_left Real.exp_one_lt_d9 (by norm_num)
        have h2 : (256 : ℝ) / 729 * 2.7182818286 < 1 := by norm_num
        linarith
      exact hlt.le
    calc (3 : ℝ) ^ (8 * G) * ((2 / 3) ^ 8) ^ m
        ≤ (3 : ℝ) ^ (2 * m) * ((2 / 3) ^ 8) ^ m := hstep1
      _ = ((256 : ℝ) / 729) ^ m := hcollapse
      _ ≤ (Real.exp (-1)) ^ m := pow_le_pow_left₀ (by norm_num) hbase m
  have hnonneg1 : 0 ≤ (3 : ℝ) ^ G * (2 / 3) ^ m := by positivity
  have hnonneg2 : 0 ≤ Real.exp (-(m : ℝ) / 8) := (Real.exp_pos _).le
  exact hdiv.trans ((pow_le_pow_iff_left₀ hnonneg1 hnonneg2 (by norm_num : (8 : ℕ) ≠ 0)).mp h8main)
