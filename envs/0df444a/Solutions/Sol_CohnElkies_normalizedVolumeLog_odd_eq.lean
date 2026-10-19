-- Prove2me | solution 1 for CohnElkies.normalizedVolumeLog_odd_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/7e626c80-0a66-491f-b2f9-10c5c357c90e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_unitBallVolume_odd_factorial

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution (k : ℕ) (hk : 0 < k) :
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
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hodd : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hkfactorial : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos k))
  have hoddfactorial : ((2 * k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos (2 * k + 1)))
  have hpipow : Real.pi ^ k ≠ (0 : ℝ) :=
    pow_ne_zero k Real.pi_ne_zero
  have htwopow : (2 : ℝ) ^ (2 * k + 1) ≠ 0 := by positivity
  unfold normalizedVolumeLog
  rw [unitBallVolume_odd_factorial,
    Real.log_div
      (mul_ne_zero (mul_ne_zero hpipow htwopow) hkfactorial)
      hoddfactorial,
    Real.log_mul (mul_ne_zero hpipow htwopow) hkfactorial,
    Real.log_mul hpipow htwopow,
    Real.log_pow, Real.log_pow]
  push_cast
  field_simp
  ring
end CohnElkies
