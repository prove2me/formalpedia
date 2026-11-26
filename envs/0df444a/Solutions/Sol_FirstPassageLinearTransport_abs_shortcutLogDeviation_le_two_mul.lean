-- Prove2me | solution 1 for FirstPassageLinearTransport.abs_shortcutLogDeviation_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:57.603543+00:00
-- url     : https://prove2.me/submissions/54bca948-8e16-40a9-85c2-fdcf68bd6f59

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrection_nonneg
import Theorems.Thm_FirstPassageLinearTransport_orbit_eq_normalizedCorrection
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_two_pow_mul
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n j : ℕ} (hn : 0 < n) :
    |shortcutLogDeviation n j| ≤ 2 * (j : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have horbit : 0 < orbit j n := orbit_pos hn j
  have horbitR : (0 : ℝ) < orbit j n := by exact_mod_cast horbit
  have hcorr := normalizedCorrection_nonneg j n
  have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ oddCount n j := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  have hlower : (n : ℝ) / (2 : ℝ) ^ j ≤ (orbit j n : ℝ) := by
    rw [orbit_eq_normalizedCorrection]
    have hbase : (n : ℝ) / (2 : ℝ) ^ j ≤
        (n : ℝ) / (2 : ℝ) ^ j + normalizedCorrection j n :=
      le_add_of_nonneg_right hcorr
    exact hbase.trans (le_mul_of_one_le_right (by positivity) hthree)
  have hlowerPos : 0 < (n : ℝ) / (2 : ℝ) ^ j := by positivity
  have hlowerLog := Real.log_le_log hlowerPos hlower
  have hupperNat := orbit_le_two_pow_mul j n
  have hupper : (orbit j n : ℝ) ≤ (2 : ℝ) ^ j * (n : ℝ) := by
    exact_mod_cast hupperNat
  have hupperLog := Real.log_le_log horbitR hupper
  rw [Real.log_div hnR.ne' (by positivity), Real.log_pow] at hlowerLog
  rw [Real.log_mul (by positivity : (0 : ℝ) < (2 : ℝ) ^ j).ne' hnR.ne',
    Real.log_pow] at hupperLog
  have hlogTwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwo1 : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hgap0 := driftGap_pos
  have hgap1 : driftGap < 1 := by
    unfold driftGap
    linarith [a0_pos]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rw [shortcutLogDeviation, abs_le]
  constructor <;> nlinarith
end FirstPassageLinearTransport
