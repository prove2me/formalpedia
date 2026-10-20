-- Prove2me | solution 2 for CohnElkies.tendsto_normalizedVolumeLog_odd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:18:08.505981+00:00
-- url     : https://prove2.me/submissions/ccb97e31-72f2-4bd6-8cc6-68b2bc396d16

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedVolumeLog_odd_eq
import Theorems.Thm_CohnElkies_tendsto_log_factorial_div_nat_sub_log_nat
import Theorems.Thm_CohnElkies_tendsto_log_nat_div_oddDimension
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology


theorem solution :
    Tendsto (fun k : ℕ => normalizedVolumeLog (2 * k + 1))
      atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  have hq : Tendsto (fun k : ℕ => (k : ℝ) / (2 * (k : ℝ) + 1)) atTop (nhds (1 / 2)) := by
    have h : Tendsto (fun k : ℕ => (1 : ℝ) / (2 + 1 / (k : ℝ))) atTop (nhds (1 / (2 + 0))) := by
      refine tendsto_const_nhds.div (tendsto_const_nhds.add ?_) (by norm_num)
      have h0 := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).comp
        tendsto_natCast_atTop_atTop
      simp only [one_div]
      exact h0
    rw [show (1:ℝ) / (2 + 0) = 1 / 2 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    field_simp
  have hF := CohnElkies.tendsto_log_factorial_div_nat_sub_log_nat
  have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun k => show id k ≤ 2 * k + 1 by simp only [id]; omega) Filter.tendsto_id
  have hF2 : Tendsto (fun k : ℕ => Real.log ((2 * k + 1).factorial : ℝ) / (2 * (k : ℝ) + 1) -
      Real.log (2 * (k : ℝ) + 1)) atTop (nhds (-1)) := by
    have := hF.comp hodd
    refine this.congr (fun k => ?_)
    simp only [Function.comp]
    push_cast
    ring_nf
  have hL := CohnElkies.tendsto_log_nat_div_oddDimension
  have h5 : Tendsto (fun k : ℕ => ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) * Real.log (k : ℝ))
      atTop (nhds 0) := by
    have := hL.const_mul (-(1 / 2 : ℝ))
    rw [mul_zero] at this
    refine this.congr (fun k => ?_)
    have hd : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have h6 : Tendsto (fun k : ℕ => (1 / 2 : ℝ) * (Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1)))
      atTop (nhds ((1 / 2 : ℝ) * Real.log (1 / 2))) := by
    have hc := ((Real.continuousAt_log (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp hq).const_mul (1 / 2 : ℝ)
    refine hc.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    simp only [Function.comp]
    rw [Real.log_div hk'.ne' (by positivity)]
  have hsum := ((((((hq.mul_const (Real.log Real.pi)).add_const (Real.log 2)).add
    (hq.mul hF)).sub hF2).add h5).add h6)
  have hlim : 1 / 2 * Real.log Real.pi + Real.log 2 + 1 / 2 * -1 - -1 + 0 + 1 / 2 * Real.log (1 / 2) =
      (Real.log (2 * Real.pi) + 1) / 2 := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', one_div, Real.log_inv]
    ring
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  rw [CohnElkies.normalizedVolumeLog_odd_eq k hk]

