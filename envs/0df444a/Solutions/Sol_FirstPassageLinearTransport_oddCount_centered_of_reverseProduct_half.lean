-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_centered_of_reverseProduct_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:24:20.946426+00:00
-- url     : https://prove2.me/submissions/0e2442cb-7a19-4e28-a6f0-3df682031f7c

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_le_one
import Theorems.Thm_FirstPassageLinearTransport_reverse_product_identity


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n j : ℕ} {E : ℝ}
    (hn : 0 < n)
    (hP : (1 / 2 : ℚ) ≤ reverseProduct n j)
    (hdev : |shortcutLogDeviation n j| ≤ E) :
    |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤
      (E + Real.log 2) / Real.log 3 := by
  have horbit : 0 < orbit j n := orbit_pos hn j
  have hPposQ : (0 : ℚ) < reverseProduct n j :=
    (by norm_num : (0 : ℚ) < 1 / 2).trans_le hP
  have hPpos : (0 : ℝ) < (reverseProduct n j : ℝ) := by
    exact_mod_cast hPposQ
  have hPupQ := reverseProduct_le_one hn j
  have hPup : (reverseProduct n j : ℝ) ≤ 1 := by exact_mod_cast hPupQ
  have hidQ := reverse_product_identity hn j
  have hidR : (n : ℝ) =
      (((2 : ℝ) ^ j * (orbit j n : ℝ)) /
        (3 : ℝ) ^ oddCount n j) * (reverseProduct n j : ℝ) := by
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hidQ
    norm_num only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow] at hcast
    exact hcast
  have hlogId := congrArg Real.log hidR
  rw [Real.log_mul (by positivity) hPpos.ne',
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt horbit)),
    Real.log_pow, Real.log_pow] at hlogId
  have hPcast : (((1 / 2 : ℚ) : ℝ)) ≤ (reverseProduct n j : ℝ) :=
    Rat.cast_le.2 hP
  norm_num at hPcast
  have hlogPLo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hPcast
  have hlogPUp := Real.log_nonpos hPpos.le hPup
  rw [show (1 / 2 : ℝ) = 1 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlogPLo
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hgaplog : driftGap * Real.log 2 =
      Real.log 2 - Real.log 3 / 2 := by
    unfold driftGap a0 logTwoThree
    field_simp [hlog2.ne']
  have hidentity :
      ((oddCount n j : ℝ) - (j : ℝ) / 2) * Real.log 3 =
        shortcutLogDeviation n j + Real.log (reverseProduct n j : ℝ) := by
    rw [shortcutLogDeviation]
    nlinarith
  have hdevBounds := abs_le.mp hdev
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hlog3]
    rw [hidentity]
    nlinarith
  · rw [le_div_iff₀ hlog3]
    rw [hidentity]
    nlinarith
end FirstPassageLinearTransport
