-- Prove2me | solution 1 for CohnElkies.tendsto_normalizedVolumeLog_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/c1b0aefd-7d76-4b1a-b5b7-bac15023da13

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_unitBallVolume_even
import Theorems.Thm_CohnElkies_tendsto_log_factorial_div_nat_sub_log_nat

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Tendsto (fun k : ℕ => normalizedVolumeLog (2 * k))
      atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
  have hcore :=
    (tendsto_const_nhds
      (x := Real.log (2 * Real.pi) / 2)).sub
      (tendsto_log_factorial_div_nat_sub_log_nat.const_mul
        (1 / 2 : ℝ))
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          Real.log (2 * Real.pi) / 2 -
            (1 / 2 : ℝ) *
              (Real.log (k.factorial : ℝ) / (k : ℝ) -
                Real.log (k : ℝ)))
        atTop (nhds ((Real.log (2 * Real.pi) + 1) / 2)) := by
    convert! hcore using 1; norm_num; ring
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  have hkfactorial : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos k))
  have hpipow : Real.pi ^ k ≠ (0 : ℝ) :=
    pow_ne_zero k Real.pi_ne_zero
  unfold normalizedVolumeLog
  rw [unitBallVolume_even,
    Real.log_div hpipow hkfactorial,
    Real.log_pow,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  push_cast
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hkreal]
  field_simp
  ring
end CohnElkies
