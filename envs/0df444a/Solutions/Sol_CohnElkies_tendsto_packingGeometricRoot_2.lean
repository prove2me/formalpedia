-- Prove2me | solution 2 for CohnElkies.tendsto_packingGeometricRoot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:20:25.65903+00:00
-- url     : https://prove2.me/submissions/5ac6ae03-8f72-4d94-ab3f-7482b4169309

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_normalizedVolumeLog
import Theorems.Thm_CohnElkies_log_normalizedVolumeRoot
import Theorems.Thm_CohnElkies_normalizedVolumeRoot_pos
import Theorems.Thm_CohnElkies_packingGeometricRoot_eq_normalizedVolumeRoot_div_two
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
theorem h47_nvr : Tendsto CohnElkies.normalizedVolumeRoot atTop
    (nhds (Real.sqrt (2 * Real.pi * Real.exp 1))) := by
  have h := (Real.continuous_exp.tendsto _).comp CohnElkies.tendsto_normalizedVolumeLog
  have hval : Real.exp ((Real.log (2 * Real.pi) + 1) / 2) = Real.sqrt (2 * Real.pi * Real.exp 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_log (by positivity : (0:ℝ) < 2 * Real.pi * Real.exp 1),
      ← Real.exp_mul, Real.log_mul (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
    congr 1; ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with d hd
  simp only [Function.comp]
  rw [← CohnElkies.log_normalizedVolumeRoot hd, Real.exp_log (CohnElkies.normalizedVolumeRoot_pos hd)]

theorem solution :
    Tendsto packingGeometricRoot atTop
      (nhds (Real.sqrt (2 * Real.pi * Real.exp 1) / 2)) := by
  refine (h47_nvr.div_const 2).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with d hd
  rw [CohnElkies.packingGeometricRoot_eq_normalizedVolumeRoot_div_two hd]

