-- Prove2me | solution 2 for CohnElkies.normalizedVolumeLog_odd_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:06.427894+00:00
-- url     : https://prove2.me/submissions/e6e0ed93-4e9b-4544-8810-a2481a0ceff5

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


theorem solution (k : ℕ) (hk : 0 < k) :
    normalizedVolumeLog (2 * k + 1) =
      (k : ℝ) / (2 * (k : ℝ) + 1) * Real.log Real.pi +
      Real.log 2 +
      ((k : ℝ) / (2 * (k : ℝ) + 1)) *
        (Real.log (k.factorial : ℝ) / (k : ℝ) -
          Real.log (k : ℝ)) -
      (Real.log ((2 * k + 1).factorial : ℝ) /
          (2 * (k : ℝ) + 1) -
        Real.log (2 * (k : ℝ) + 1)) +
      ((k : ℝ) / (2 * (k : ℝ) + 1) - (1 / 2 : ℝ)) *
        Real.log (k : ℝ) +
      (1 / 2 : ℝ) *
        (Real.log (k : ℝ) - Real.log (2 * (k : ℝ) + 1)) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have hp := Real.pi_pos
  have hFnat : (2 * k + 1).factorial = (2 * k + 1).doubleFactorial * (2 ^ k * k.factorial) := by
    rw [Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  have hF : ((2 * k + 1).factorial : ℝ) =
      ((2 * k + 1).doubleFactorial : ℝ) * (2 ^ k * (k.factorial : ℝ)) := by exact_mod_cast hFnat
  have hDpos : (0:ℝ) < ((2 * k + 1).doubleFactorial : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  have hfpos : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hLF : Real.log ((2 * k + 1).factorial : ℝ) =
      Real.log ((2 * k + 1).doubleFactorial : ℝ) + k * Real.log 2 + Real.log (k.factorial : ℝ) := by
    rw [hF, Real.log_mul hDpos.ne' (by positivity), Real.log_mul (by positivity) hfpos.ne',
      Real.log_pow]
    ring
  have hG : Real.Gamma (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) =
      ((2 * k + 1 : ℕ).doubleFactorial : ℝ) * Real.sqrt Real.pi / 2 ^ (k + 1) := by
    rw [show ((2 * k + 1 : ℕ) : ℝ) / 2 + 1 = (k : ℝ) + 1 + 1 / 2 by push_cast; ring]
    exact Real.Gamma_nat_add_one_add_half k
  have hV : Real.log (unitBallVolume (2 * k + 1)) =
      ((2 * (k:ℝ) + 1) / 2) * Real.log Real.pi -
        (Real.log ((2 * k + 1).doubleFactorial : ℝ) + Real.log Real.pi / 2 -
          (k + 1) * Real.log 2) := by
    unfold unitBallVolume
    rw [hG, Real.log_div (by positivity) (by positivity), Real.log_rpow hp,
      Real.log_div (by positivity) (by positivity), Real.log_mul hDpos.ne' (by positivity),
      Real.log_sqrt hp.le, Real.log_pow]
    push_cast
    ring
  unfold normalizedVolumeLog
  rw [hV, hLF]
  push_cast
  field_simp
  ring

