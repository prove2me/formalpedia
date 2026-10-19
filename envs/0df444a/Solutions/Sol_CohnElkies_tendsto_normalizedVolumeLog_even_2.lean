-- Prove2me | solution 2 for CohnElkies.tendsto_normalizedVolumeLog_even
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:42.276329+00:00
-- url     : https://prove2.me/submissions/bde8be75-531f-404c-91d8-de17f8200c85

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
theorem h47_log_factorial_eq (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) / n - Real.log n =
      -1 + (Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2 + Real.log n / 2) / n := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsq : 0 < Real.sqrt (2 * n : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < ((n : ℝ) / Real.exp 1) := div_pos hnpos (Real.exp_pos 1)
  have hD : 0 < Real.sqrt (2 * n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := mul_pos hsq (pow_pos hq n)
  have hspos : 0 < Stirling.stirlingSeq n := by unfold Stirling.stirlingSeq; exact div_pos hf hD
  have hs : (n.factorial : ℝ) = Stirling.stirlingSeq n * (Real.sqrt (2 * n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n) := by
    unfold Stirling.stirlingSeq; field_simp
  rw [hs, Real.log_mul hspos.ne' hD.ne', Real.log_mul hsq.ne' (pow_pos hq n).ne', Real.log_pow,
    Real.log_div hnpos.ne' (Real.exp_pos 1).ne', Real.log_exp, Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) hnpos.ne']
  field_simp
  ring

theorem h47_tendsto_log_factorial :
    Tendsto (fun n : ℕ => Real.log (n.factorial : ℝ) / n - Real.log n) atTop (𝓝 (-1)) := by
  have hS : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
    simp only [pow_one, one_mul, add_zero] at this
    exact this
  have h : Tendsto (fun n : ℕ => -1 + ((Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2) * ((n : ℝ))⁻¹ +
      (Real.log (n : ℝ) / n) / 2)) atTop
      (𝓝 (-1 + ((Real.log (Real.sqrt Real.pi) + Real.log 2 / 2) * 0 + 0 / 2))) :=
    tendsto_const_nhds.add (((hS.add tendsto_const_nhds).mul hinv).add (hlog.div_const 2))
  rw [show (-1:ℝ) + ((Real.log (Real.sqrt Real.pi) + Real.log 2 / 2) * 0 + 0 / 2) = -1 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [h47_log_factorial_eq n hn]
  ring

theorem solution :
    Tendsto (fun k : ℕ => normalizedVolumeLog (2 * k))
      atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  have hpi := Real.pi_pos
  have key : ∀ k : ℕ, 0 < k → normalizedVolumeLog (2 * k) =
      Real.log Real.pi / 2 + Real.log 2 / 2 -
        (Real.log (k.factorial : ℝ) / k - Real.log k) / 2 := by
    intro k hk
    have hkpos : (0:ℝ) < k := by exact_mod_cast hk
    have hf : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hV : unitBallVolume (2 * k) = Real.pi ^ k / (k.factorial : ℝ) := by
      unfold unitBallVolume
      push_cast
      rw [show (2 * (k:ℝ)) / 2 = (k:ℝ) by ring, Real.rpow_natCast, Real.Gamma_nat_eq_factorial]
    unfold normalizedVolumeLog
    rw [hV, Real.log_div (pow_pos hpi k).ne' hf.ne', Real.log_pow]
    push_cast
    rw [Real.log_mul (by norm_num) hkpos.ne']
    field_simp
    ring
  have h := (tendsto_const_nhds (x := Real.log Real.pi / 2 + Real.log 2 / 2)).sub
    (h47_tendsto_log_factorial.div_const 2)
  rw [show Real.log Real.pi / 2 + Real.log 2 / 2 - (-1) / 2 = (Real.log (2 * Real.pi) + 1) / 2 by
    rw [Real.log_mul (by norm_num) hpi.ne']; ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [key k hk]

