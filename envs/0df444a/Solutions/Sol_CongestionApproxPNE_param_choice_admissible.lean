-- Prove2me | solution 1 for CongestionApproxPNE.param_choice_admissible
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:07:02.056765+00:00
-- url     : https://prove2.me/submissions/1e0aab1d-4d6d-4ecb-bf48-672a1f23a734

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

open CongestionApproxPNE in
theorem solution (d : ℕ) (hd : 4 ≤ d) :
    1 ≤ kd d ∧ kd d ≤ d ∧ 0 ≤ wChoice d ∧ wChoice d ≤ 1 ∧ 0 ≤ betaChoice d ∧ betaChoice d ≤ 1 := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hL4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hL : 4 / 3 < Real.log d := by
    have : Real.log 4 ≤ Real.log d := Real.log_le_log (by norm_num) hdR
    linarith
  have hLpos : 0 < Real.log d := by linarith
  have hLL : 1 / 4 ≤ Real.log (Real.log d) := by
    have h := Real.one_sub_inv_le_log_of_pos hLpos
    have : (Real.log d)⁻¹ ≤ 3 / 4 := by
      rw [inv_le_comm₀ hLpos (by norm_num)]; linarith
    linarith
  have hLd : Real.log d ≤ d / 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < d / 2 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold kd
    rw [Nat.one_le_ceil_iff]
    apply div_pos hLpos
    linarith
  · unfold kd
    rw [Nat.ceil_le]
    have hden : (1 / 2 : ℝ) ≤ 2 * Real.log (Real.log d) := by linarith
    calc Real.log d / (2 * Real.log (Real.log d)) ≤ Real.log d / (1 / 2) :=
          div_le_div_of_nonneg_left hLpos.le (by norm_num) hden
      _ ≤ d := by linarith
  · unfold wChoice
    positivity
  · unfold wChoice
    rw [div_le_one (by positivity)]
    linarith
  · unfold betaChoice
    have h1 : 0 < (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) := Real.rpow_pos_of_pos hd0 _
    have h2 : 0 < (1 + wChoice d) ^ d := by
      apply pow_pos
      unfold wChoice; positivity
    positivity
  · unfold betaChoice
    have h1 : 1 ≤ (d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) :=
      Real.one_le_rpow (by linarith) (by positivity)
    have hw : 0 ≤ wChoice d := by unfold wChoice; positivity
    have h2 : 1 ≤ (1 + wChoice d) ^ d := one_le_pow₀ (by linarith)
    rw [div_le_one (by positivity)]
    nlinarith
