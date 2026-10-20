-- Prove2me | solution 2 for CohnElkies.tendsto_normalizedVolumeRoot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:20:15.028123+00:00
-- url     : https://prove2.me/submissions/997b4153-eddc-4888-9cbc-ba4e5190c723

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_normalizedVolumeLog
import Theorems.Thm_CohnElkies_log_normalizedVolumeRoot
import Theorems.Thm_CohnElkies_normalizedVolumeRoot_pos
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
    Tendsto normalizedVolumeRoot atTop
      (nhds (Real.sqrt (2 * Real.pi * Real.exp 1))) := by
  exact h47_nvr

