-- Prove2me | solution 2 for CohnElkies.tendsto_log_factorial_div_nat_sub_log_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:12:19.557889+00:00
-- url     : https://prove2.me/submissions/09e420ee-d30b-4f42-8abf-54e3ac75d621

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology


theorem solution :
    Tendsto
      (fun k : ℕ =>
        Real.log (k.factorial : ℝ) / (k : ℝ) - Real.log (k : ℝ))
      atTop (nhds (-1)) := by
  have h1 : Tendsto (fun k : ℕ => Real.log (Stirling.stirlingSeq k) / (k : ℝ)) atTop (nhds 0) := by
    have h := Stirling.tendsto_stirlingSeq_sqrt_pi
    have hl := (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp h
    exact hl.div_atTop tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun k : ℕ => Real.log ((2 : ℝ) * (k : ℝ)) / (k : ℝ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ => Real.log (k:ℝ) / (k:ℝ)) atTop (nhds 0) :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop |>.congr (fun k => by simp)
    have h2 : Tendsto (fun k : ℕ => Real.log 2 / (k:ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine (by simpa using h2.add h1 : Tendsto (fun k : ℕ => Real.log 2 / (k:ℝ) + Real.log (k:ℝ) / (k:ℝ)) atTop (nhds 0)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    rw [Real.log_mul (by norm_num) (by positivity), add_div]
  have h3 := (h1.add (h2.const_mul (1/2))).sub_const 1
  simp only [mul_zero, add_zero, zero_sub] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hf : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [Stirling.stirlingSeq, Real.log_div hf.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hk'.ne' (Real.exp_pos 1).ne', Real.log_exp]
  field_simp
  ring

