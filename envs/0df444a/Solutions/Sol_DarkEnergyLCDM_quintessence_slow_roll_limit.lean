-- Prove2me | solution 1 for DarkEnergyLCDM.quintessence_slow_roll_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:14.03593+00:00
-- url     : https://prove2.me/submissions/159638fe-a19a-4784-8ff8-ba71080cda5f

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Filter Topology
open DarkEnergyLCDM

theorem solution (V : ℝ) (hV : V ≠ 0) :
    Tendsto (fun ϕdot : ℝ => quintessenceEOS ϕdot V) (𝓝 0) (𝓝 (-1)) := by
  unfold quintessenceEOS
  have h : (-1 : ℝ) = ((0:ℝ) ^ 2 / 2 - V) / ((0:ℝ) ^ 2 / 2 + V) := by
    field_simp; ring
  rw [h]
  apply ContinuousAt.tendsto
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  simpa using hV
