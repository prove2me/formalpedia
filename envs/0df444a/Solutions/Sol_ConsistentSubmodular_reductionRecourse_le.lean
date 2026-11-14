-- Prove2me | solution 1 for ConsistentSubmodular.reductionRecourse_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:30:46.173542+00:00
-- url     : https://prove2.me/submissions/fa5cd53b-a88e-48cf-a6cd-643a848212a7

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RecourseBound

section

namespace ConsistentSubmodular

theorem windowTestBound_pos (N S : ℕ) : 0 < windowTestBound N S := by
  unfold windowTestBound
  positivity

end ConsistentSubmodular

end

section

noncomputable section

namespace ConsistentSubmodular

theorem logBudget_le_log (x : ℕ) (hx : 1 ≤ x) : (logBudget x : ℝ) ≤ 2 * Real.log x + 1 := by
  unfold logBudget
  push_cast
  have hpow : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  have hpowr : (2 : ℝ) ^ Nat.log 2 x ≤ x := by exact_mod_cast hpow
  have hlog : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by positivity) hpowr
    rwa [Real.log_pow] at h
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnn : (0 : ℝ) ≤ Nat.log 2 x := Nat.cast_nonneg _
  nlinarith

theorem log_succ_le {N : ℕ} (hN : 1 ≤ N) : Real.log ((N : ℝ) + 1) ≤ 1 + Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2N : (N : ℝ) + 1 ≤ 2 * N := by linarith
  have h := Real.log_le_log (by positivity) h2N
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  linarith [Real.log_two_lt_d9]

theorem window_logBudget_le (C N : ℕ) (hN : 1 ≤ N) :
    (logBudget (4 * windowTestBound N ((C + 1) * (3 * N + 2))) : ℝ) ≤
      2 * Real.log (1200 * ((C : ℝ) + 1)) + 7 + 6 * Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : (1 : ℝ) ≤ (C : ℝ) + 1 := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
  have hnat : 4 * windowTestBound N ((C + 1) * (3 * N + 2)) ≤ 1200 * (C + 1) * (N + 1) ^ 3 := by
    unfold windowTestBound
    have h : (C + 1) * (3 * N + 2) + 1 ≤ 3 * (C + 1) * (N + 1) := by nlinarith
    calc 4 * (100 * (N + 1) ^ 2 * ((C + 1) * (3 * N + 2) + 1))
        = 400 * (N + 1) ^ 2 * ((C + 1) * (3 * N + 2) + 1) := by ring
      _ ≤ 400 * (N + 1) ^ 2 * (3 * (C + 1) * (N + 1)) := Nat.mul_le_mul_left _ h
      _ = 1200 * (C + 1) * (N + 1) ^ 3 := by ring
  have hx1 : 1 ≤ 4 * windowTestBound N ((C + 1) * (3 * N + 2)) := by
    have := windowTestBound_pos N ((C + 1) * (3 * N + 2))
    omega
  have hreal : ((4 * windowTestBound N ((C + 1) * (3 * N + 2)) : ℕ) : ℝ) ≤
      1200 * ((C : ℝ) + 1) * ((N : ℝ) + 1) ^ 3 := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by exact_mod_cast hx1) hreal
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hsucc := log_succ_le hN
  have hb := logBudget_le_log _ hx1
  push_cast at hlog hsucc hb
  linarith

theorem bridge_logBudget_le (N : ℕ) (hN : 1 ≤ N) :
    (logBudget (4 * (2 * N + 1)) : ℝ) ≤ 7 + 2 * Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ 4 * (2 * N + 1) := by omega
  have hreal : ((4 * (2 * N + 1) : ℕ) : ℝ) ≤ 12 * N := by push_cast; linarith
  have hlog := Real.log_le_log (by exact_mod_cast hx1) hreal
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have h12 : Real.log 12 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    nlinarith [pow_le_pow_left₀ (by norm_num) he.le 3]
  have hb := logBudget_le_log _ hx1
  linarith

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution (C N : ℕ) (hN : 1 ≤ N) :
    (reductionRecourse N ((C + 1) * (3 * N + 2)) : ℝ) ≤
      (N : ℝ) ^ 3 * (rateConstant C + 800 * Real.log N) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hw := mul_le_mul_of_nonneg_left (window_logBudget_le C N hN) hN3
  have hb := mul_le_mul_of_nonneg_left (bridge_logBudget_le N hN) hN3
  have hlist : 4 * N * (4 * N + 1) * (3 * familyLength ((C + 1) * (3 * N + 2)) + 1) ≤
      31220 * (C + 1) * N ^ 3 := by
    unfold familyLength windowLengthBound
    have h1 : 4 * N * (4 * N + 1) ≤ 20 * N ^ 2 := by nlinarith
    have h2 : 3 * (100 * ((C + 1) * (3 * N + 2)) + 10 + 10) + 1 ≤ 1561 * (C + 1) * N := by
      nlinarith
    calc 4 * N * (4 * N + 1) * (3 * (100 * ((C + 1) * (3 * N + 2)) + 10 + 10) + 1)
        ≤ 20 * N ^ 2 * (1561 * (C + 1) * N) := Nat.mul_le_mul h1 h2
      _ = 31220 * (C + 1) * N ^ 3 := by ring
  have hlistr : ((4 * N * (4 * N + 1) * (3 * familyLength ((C + 1) * (3 * N + 2)) + 1) : ℕ) : ℝ) ≤
      31220 * ((C : ℝ) + 1) * (N : ℝ) ^ 3 := by exact_mod_cast hlist
  have hsmall : 2 * (N : ℝ) * (2 * (4 * N + 1) + 2) + 2 ≤ 26 * (N : ℝ) ^ 3 := by
    have h12 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h23 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith
    have h03 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
    nlinarith
  unfold reductionRecourse transferThreshold familyHeavy windowHeavyBound bridgeHeavy
  push_cast at hlistr ⊢
  unfold rateConstant
  nlinarith

end
