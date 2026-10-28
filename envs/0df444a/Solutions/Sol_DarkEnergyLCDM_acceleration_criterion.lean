-- Prove2me | solution 1 for DarkEnergyLCDM.acceleration_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:56.903706+00:00
-- url     : https://prove2.me/submissions/b0e1394c-a4e3-472e-a4be-6d7a1da75cdd

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Real
open DarkEnergyLCDM

theorem solution (G Λ : ℝ) (a ρ p : ℝ → ℝ) (t : ℝ) (ha : 0 < a t)
    (hacc : AccelerationEq G Λ a ρ p t) :
    0 < deriv (deriv a) t ↔ 4 * π * G * (ρ t + 3 * p t) < Λ := by
  unfold AccelerationEq at hacc
  rw [← div_pos_iff_of_pos_right ha, hacc]
  constructor <;> intro h <;> linarith
