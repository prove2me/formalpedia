-- Prove2me | solution 1 for FirstPassageLinearTransport.abs_rawLogDeviation_rawTime_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:29.715745+00:00
-- url     : https://prove2.me/submissions/be9116a3-50da-413b-9003-4ba94799789c

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawOddDeviationCoefficient_nonneg
import Theorems.Thm_FirstPassageLinearTransport_rawLogDeviation_rawTime

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n j : ℕ} {E F : ℝ}
    (hshortcut : |shortcutLogDeviation n j| ≤ E)
    (hodd : |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    |rawLogDeviation n (rawTime n j)| ≤
      E + rawOddDeviationCoefficient * F := by
  rw [rawLogDeviation_rawTime]
  have habs := abs_add_le (shortcutLogDeviation n j)
    (rawOddDeviationCoefficient *
      ((oddCount n j : ℝ) - (j : ℝ) / 2))
  have hcoef0 := rawOddDeviationCoefficient_nonneg
  rw [abs_mul, abs_of_nonneg hcoef0] at habs
  nlinarith [mul_le_mul_of_nonneg_left hodd hcoef0]
end FirstPassageLinearTransport
