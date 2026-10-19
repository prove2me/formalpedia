-- Prove2me | solution 2 for CohnElkies.unitBallVolume_odd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:02.337878+00:00
-- url     : https://prove2.me/submissions/378e482d-45a7-4849-aa08-731cfe1500d0

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


theorem solution (k : ℕ) :
    unitBallVolume (2 * k + 1) =
      Real.pi ^ k * (2 : ℝ) ^ (2 * k + 1) * (k.factorial : ℝ) /
        ((2 * k + 1).factorial : ℝ) := by
  unfold unitBallVolume
  have hk : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hk2 : (0:ℝ) < ((2 * k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hdup := Real.Gamma_mul_Gamma_add_half ((k:ℝ) + 1)
  rw [Real.Gamma_nat_eq_factorial,
    show (2:ℝ) * ((k:ℝ) + 1) = ((2 * k + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial,
    show (1:ℝ) - (((2 * k + 1 : ℕ) : ℝ) + 1) = -((2 * k + 1 : ℕ) : ℝ) by ring,
    Real.rpow_neg (by norm_num), Real.rpow_natCast] at hdup
  have hG : Real.Gamma ((k:ℝ) + 1 + 1 / 2) =
      (((2 * k + 1).factorial : ℝ) * ((2:ℝ) ^ (2 * k + 1))⁻¹ * Real.sqrt Real.pi) /
        (k.factorial : ℝ) := by
    rw [eq_div_iff hk.ne', mul_comm]; exact hdup
  push_cast
  rw [show (2 * (k:ℝ) + 1) / 2 + 1 = (k:ℝ) + 1 + 1 / 2 by ring,
    show (2 * (k:ℝ) + 1) / 2 = (k:ℝ) + 1 / 2 by ring,
    Real.rpow_add Real.pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow, hG]
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

