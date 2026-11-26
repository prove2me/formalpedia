-- Prove2me | solution 1 for FirstPassageLinearTransport.abs_shortcutLogDeviation_le_of_initialWindowGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:31.023318+00:00
-- url     : https://prove2.me/submissions/5cdf4d0d-3468-4e72-b983-06b006384a23

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_eq_two_rpow_neg_gap
import Theorems.Thm_FirstPassageLinearTransport_centralOrbitScale_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {t : ℝ} {n j : ℕ}
    (hn : 0 < n)
    (hnGood : n ∈ initialWindowGood t)
    (hj : j ≤ Nat.log 2 n) :
    |shortcutLogDeviation n j| ≤ t * Real.log n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have horbit : 0 < orbit j n := orbit_pos hn j
  have horbitR : (0 : ℝ) < orbit j n := by exact_mod_cast horbit
  have henv := hnGood j hj
  have hlowerLog := Real.log_le_log
    (mul_pos (centralOrbitScale_pos j)
      (Real.rpow_pos_of_pos hnR (1 - t))) henv.1
  have hupperLog := Real.log_le_log horbitR henv.2
  rw [Real.log_mul (centralOrbitScale_pos j).ne'
      (Real.rpow_pos_of_pos hnR (1 - t)).ne',
    centralOrbitScale_eq_two_rpow_neg_gap,
    Real.log_rpow (by norm_num), Real.log_rpow hnR] at hlowerLog
  rw [Real.log_mul (centralOrbitScale_pos j).ne'
      (Real.rpow_pos_of_pos hnR (1 + t)).ne',
    centralOrbitScale_eq_two_rpow_neg_gap,
    Real.log_rpow (by norm_num), Real.log_rpow hnR] at hupperLog
  rw [shortcutLogDeviation, abs_le]
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  constructor <;> nlinarith [Real.log_nonneg hn1]
end FirstPassageLinearTransport
