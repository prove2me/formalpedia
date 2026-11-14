-- Prove2me | solution 1 for GaussMixGated.ExactReal.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @ligracew
-- created : 2026-11-13T07:58:04.195514+00:00
-- url     : https://prove2.me/submissions/e99c15aa-488d-459c-8d5c-b68a6f4059cb

import Definitions.Def_GaussMixGated_ExactReal_Schedule

open GaussMixGated.ExactReal

private lemma log_four_pos' : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)

private lemma four_pow_ge_of_ceil {x : ℝ} {J : ℕ}
    (hJ : J = ⌈Real.log x / Real.log 4⌉₊) (hx : 0 < x) :
    x ≤ (4 : ℝ) ^ J := by
  have h1 : Real.log x / Real.log 4 ≤ (J : ℝ) := by
    rw [hJ]
    exact Nat.le_ceil _
  have h2 : Real.log x ≤ (J : ℝ) * Real.log 4 :=
    (div_le_iff₀ log_four_pos').mp h1
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ Real.exp ((J : ℝ) * Real.log 4) := Real.exp_le_exp.mpr h2
    _ = (Real.exp (Real.log 4)) ^ J := Real.exp_nat_mul (Real.log 4) J
    _ = (4 : ℝ) ^ J := by rw [Real.exp_log (by norm_num)]

private lemma exp_one_gt_27 : (2.7 : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  linarith

private lemma log_le_half_self {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have h1 := Real.add_one_le_exp (Real.log (y / 2))
  rw [Real.exp_log (by linarith)] at h1
  have hlog2 : Real.log (y / 2) = Real.log y - Real.log 2 :=
    Real.log_div hy.ne' (by norm_num)
  have hlog2_lt_1 : Real.log 2 < 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) (lt_trans (by norm_num : (2 : ℝ) < 2.7) exp_one_gt_27)
  linarith

private lemma log_16_lt_3 : Real.log 16 < 3 := by
  have he3 : (16 : ℝ) < Real.exp 3 := by
    calc (16 : ℝ) < (2.7 : ℝ) ^ (3 : ℕ) := by norm_num
      _ < (Real.exp 1) ^ (3 : ℕ) := pow_lt_pow_left₀ exp_one_gt_27 (by norm_num) (by norm_num)
      _ = Real.exp ((3 : ℕ) * (1 : ℝ)) := (Real.exp_nat_mul 1 3).symm
      _ = Real.exp 3 := by norm_num
  rw [← Real.log_exp 3]
  exact Real.log_lt_log (by norm_num) he3

private lemma log_8_lt_3 : Real.log 8 < 3 :=
  lt_trans (Real.log_lt_log (by norm_num) (by norm_num : (8 : ℝ) < 16)) log_16_lt_3

private lemma r0_sq_bound (d N0 : ℕ) (δ : ℝ) (hN0 : 1 ≤ N0) (hδ : 0 < δ) (hδ' : δ < 1 / 4) :
    (Real.sqrt (d : ℝ) + Real.sqrt (2 * Real.log (16 * (N0 : ℝ) / δ))) ^ 2 ≤
      2 * (d : ℝ) + 4 * Real.log (16 * (N0 : ℝ) / δ) := by
  have hlog_nonneg : 0 ≤ Real.log (16 * (N0 : ℝ) / δ) := by
    apply Real.log_nonneg
    have hN0' : (1 : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hN0
    rw [le_div_iff₀ hδ]
    linarith
  set a := Real.sqrt (d : ℝ)
  set b := Real.sqrt (2 * Real.log (16 * (N0 : ℝ) / δ))
  have ha2 : a ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
  have hb2 : b ^ 2 = 2 * Real.log (16 * (N0 : ℝ) / δ) := Real.sq_sqrt (by linarith)
  have hab : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    have hdiff : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    linarith
  linarith

private lemma linear_combo_le (d H L : ℝ) (hd : 1 ≤ d) (hH : 0 < H) (hL : 10 < L) :
    2 * d + 4 * (3 + L + H + (3 + L + H) / 2) ≤ 32 * (d + H + 2) * L := by
  have h1 : 2 * d + 4 * (3 + L + H + (3 + L + H) / 2) = 2 * d + 6 * H + 6 * L + 18 := by ring
  rw [h1]
  have hdL : 2 * d ≤ 32 * d * L := by nlinarith
  have hHL : 6 * H ≤ 32 * H * L := by nlinarith
  have hrem : 6 * L + 18 ≤ 64 * L := by linarith
  linarith

theorem solution (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (Ccov : ℝ) (hC : 1 ≤ Ccov) :
    R0sched d k ε δ Ccov / sigmaSched d δ 0 ≤ Real.sqrt (Lstar d k ε δ Ccov) := by
  have hd_pos : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hk_pos : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hAstar : 3 ≤ Astar Ccov := by unfold Astar; linarith
  have hAstar_pos : 0 < Astar Ccov := by linarith
  have hH_pos : 0 < Hconf δ := by
    unfold Hconf
    apply Real.log_pos
    rw [lt_div_iff₀ hδ]
    linarith
  have h32_pos : 0 < 32 * ((d : ℝ) + Hconf δ + 2) := by positivity
  have h4J : 32 * ((d : ℝ) + Hconf δ + 2) ≤ (4 : ℝ) ^ Jsched d δ :=
    four_pow_ge_of_ceil rfl h32_pos
  have hJ_ge_1 : 1 ≤ Jsched d δ := by
    by_contra hJ0
    have hJ_eq : Jsched d δ = 0 := by omega
    rw [hJ_eq] at h4J
    norm_num at h4J
    linarith
  have hβ_pos : 0 < betaSched d ε δ Ccov := by
    unfold betaSched; positivity
  have hβ_lt : betaSched d ε δ Ccov < 1 / 200000 := by
    unfold betaSched
    have hA_pow_ge : (9 : ℝ) ≤ Astar Ccov ^ (Jsched d δ + 1) := by
      calc (9 : ℝ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (Jsched d δ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ Astar Ccov ^ (Jsched d δ + 1) := pow_le_pow_left₀ (by norm_num) hAstar _
    have hJ1 : (2 : ℝ) ≤ (Jsched d δ : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hJ_ge_1
    have hdenom : (18000 : ℝ) ≤ 1000 * ((Jsched d δ : ℝ) + 1) * Astar Ccov ^ (Jsched d δ + 1) := by
      nlinarith
    have hε_sq : ε ^ 2 < 1 / 16 := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hL_gt_10 : 10 < Lstar d k ε δ Ccov := by
    unfold Lstar
    have h2kβ : 400000 < 2 * (k : ℝ) / betaSched d ε δ Ccov := by
      rw [lt_div_iff₀ hβ_pos]; nlinarith
    have he10 : Real.exp 10 < 400000 := by
      have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      calc Real.exp 10 = Real.exp ((10 : ℕ) * (1 : ℝ)) := by norm_num
        _ = (Real.exp 1) ^ (10 : ℕ) := Real.exp_nat_mul 1 10
        _ < 3 ^ (10 : ℕ) := pow_lt_pow_left₀ he3 (Real.exp_pos 1).le (by norm_num)
        _ < 400000 := by norm_num
    rw [← Real.log_exp 10]
    exact Real.log_lt_log (Real.exp_pos 10) (lt_trans he10 h2kβ)
  have hlog16kδ_gt_1 : 1 < Real.log (16 * (k : ℝ) / δ) := by
    have h64 : (64 : ℝ) < 16 * (k : ℝ) / δ := by
      rw [lt_div_iff₀ hδ]; nlinarith
    have he3 : Real.exp 1 < 64 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (lt_trans he3 h64)
  have hkβ_gt_1 : 1 < ((k : ℝ) / betaSched d ε δ Ccov) * Real.log (16 * (k : ℝ) / δ) := by
    have hkβ : (200000 : ℝ) < (k : ℝ) / betaSched d ε δ Ccov := by
      rw [lt_div_iff₀ hβ_pos]; nlinarith
    nlinarith
  have hN0_ge_1 : 1 ≤ N0sched d k ε δ Ccov := by
    unfold N0sched
    exact Nat.ceil_pos.mpr (by linarith)
  have hN0_le : (N0sched d k ε δ Ccov : ℝ) ≤
      2 * ((k : ℝ) / betaSched d ε δ Ccov) * Real.log (16 * (k : ℝ) / δ) := by
    have hceil : (N0sched d k ε δ Ccov : ℝ) ≤
        ((k : ℝ) / betaSched d ε δ Ccov) * Real.log (16 * (k : ℝ) / δ) + 1 := by
      unfold N0sched
      exact (Nat.ceil_lt_add_one (by positivity)).le
    linarith
  have hlog_16kδ_le : Real.log (16 * (k : ℝ) / δ) ≤ Real.log 8 + Lstar d k ε δ Ccov + Hconf δ := by
    have h16kδ_le : 16 * (k : ℝ) / δ ≤ 8 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ) := by
      have h16kδ_eq : 16 * (k : ℝ) / δ =
          8 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * betaSched d ε δ Ccov * (1 / δ) := by
        field_simp; ring
      rw [h16kδ_eq]
      have hβ1 : betaSched d ε δ Ccov ≤ 1 := by linarith
      calc 8 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * betaSched d ε δ Ccov * (1 / δ)
          ≤ 8 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * 1 * (1 / δ) := by gcongr
        _ = 8 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ) := by ring
    calc Real.log (16 * (k : ℝ) / δ)
        ≤ Real.log (8 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ)) :=
          Real.log_le_log (by positivity) h16kδ_le
      _ = Real.log (8 * (2 * (k : ℝ) / betaSched d ε δ Ccov)) + Real.log (1 / δ) :=
          Real.log_mul (by positivity) (by positivity)
      _ = Real.log 8 + Real.log (2 * (k : ℝ) / betaSched d ε δ Ccov) + Real.log (1 / δ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
      _ = Real.log 8 + Lstar d k ε δ Ccov + Hconf δ := rfl
  have hlog_16N0_le : Real.log (16 * (N0sched d k ε δ Ccov : ℝ) / δ) ≤
      3 + Lstar d k ε δ Ccov + Hconf δ + (3 + Lstar d k ε δ Ccov + Hconf δ) / 2 := by
    have h16N0_pos : (0 : ℝ) < 16 * (N0sched d k ε δ Ccov : ℝ) / δ := by
      have : (0 : ℝ) < (N0sched d k ε δ Ccov : ℝ) := by exact_mod_cast hN0_ge_1
      positivity
    have h16N0_le : 16 * (N0sched d k ε δ Ccov : ℝ) / δ ≤
        16 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ) * Real.log (16 * (k : ℝ) / δ) := by
      calc 16 * (N0sched d k ε δ Ccov : ℝ) / δ
          = (16 / δ) * (N0sched d k ε δ Ccov : ℝ) := by ring
        _ ≤ (16 / δ) * (2 * ((k : ℝ) / betaSched d ε δ Ccov) * Real.log (16 * (k : ℝ) / δ)) := by
            gcongr
        _ = 16 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ) * Real.log (16 * (k : ℝ) / δ) := by
            ring
    have hlog_pos : 0 < Real.log (16 * (k : ℝ) / δ) := by linarith
    have hlog_log : Real.log (Real.log (16 * (k : ℝ) / δ)) ≤
        (3 + Lstar d k ε δ Ccov + Hconf δ) / 2 := by
      have h1 := log_le_half_self hlog_pos
      have h8 := log_8_lt_3
      linarith
    have h16 : Real.log 16 < 3 := log_16_lt_3
    calc Real.log (16 * (N0sched d k ε δ Ccov : ℝ) / δ)
        ≤ Real.log (16 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ) *
            Real.log (16 * (k : ℝ) / δ)) :=
          Real.log_le_log h16N0_pos h16N0_le
      _ = Real.log (16 * (2 * (k : ℝ) / betaSched d ε δ Ccov) * (1 / δ)) +
            Real.log (Real.log (16 * (k : ℝ) / δ)) :=
          Real.log_mul (by positivity) hlog_pos.ne'
      _ = Real.log (16 * (2 * (k : ℝ) / betaSched d ε δ Ccov)) + Real.log (1 / δ) +
            Real.log (Real.log (16 * (k : ℝ) / δ)) := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log 16 + Lstar d k ε δ Ccov + Hconf δ +
            Real.log (Real.log (16 * (k : ℝ) / δ)) := by
          rw [Real.log_mul (by norm_num) (by positivity)]; rfl
      _ ≤ 3 + Lstar d k ε δ Ccov + Hconf δ + (3 + Lstar d k ε δ Ccov + Hconf δ) / 2 := by
          linarith
  have hsigma0_pos : 0 < sigmaSched d δ 0 := by unfold sigmaSched; positivity
  have hsigma0_sq : (sigmaSched d δ 0) ^ 2 = (4 : ℝ) ^ Jsched d δ := by
    unfold sigmaSched
    simp only [Nat.sub_zero]
    rw [← pow_mul, mul_comm (Jsched d δ) 2, pow_mul]
    norm_num
  have hR0_nonneg : 0 ≤ R0sched d k ε δ Ccov := by unfold R0sched; positivity
  have hR0_le_prod : (R0sched d k ε δ Ccov) ^ 2 ≤
      (sigmaSched d δ 0) ^ 2 * Lstar d k ε δ Ccov := by
    have hsq : (R0sched d k ε δ Ccov) ^ 2 ≤
        2 * (d : ℝ) + 4 * Real.log (16 * (N0sched d k ε δ Ccov : ℝ) / δ) :=
      r0_sq_bound d (N0sched d k ε δ Ccov) δ hN0_ge_1 hδ hδ'
    have hlin := linear_combo_le (d : ℝ) (Hconf δ) (Lstar d k ε δ Ccov) hd_pos hH_pos hL_gt_10
    have hL_nonneg : 0 ≤ Lstar d k ε δ Ccov := by linarith
    calc (R0sched d k ε δ Ccov) ^ 2
        ≤ 2 * (d : ℝ) + 4 * Real.log (16 * (N0sched d k ε δ Ccov : ℝ) / δ) := hsq
      _ ≤ 2 * (d : ℝ) + 4 * (3 + Lstar d k ε δ Ccov + Hconf δ +
            (3 + Lstar d k ε δ Ccov + Hconf δ) / 2) := by linarith
      _ ≤ 32 * ((d : ℝ) + Hconf δ + 2) * Lstar d k ε δ Ccov := hlin
      _ ≤ (4 : ℝ) ^ Jsched d δ * Lstar d k ε δ Ccov :=
          mul_le_mul_of_nonneg_right h4J hL_nonneg
      _ = (sigmaSched d δ 0) ^ 2 * Lstar d k ε δ Ccov := by rw [hsigma0_sq]
  rw [div_le_iff₀ hsigma0_pos, ← Real.sqrt_sq hR0_nonneg]
  have hrhs : Real.sqrt (Lstar d k ε δ Ccov) * sigmaSched d δ 0 =
      Real.sqrt ((sigmaSched d δ 0) ^ 2 * Lstar d k ε δ Ccov) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsigma0_pos.le, mul_comm]
  rw [hrhs]
  exact Real.sqrt_le_sqrt hR0_le_prod
