-- Prove2me | solution 1 for FirstPassageLinearTransport.rawPrefix_log_deviation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:56.601718+00:00
-- url     : https://prove2.me/submissions/8b314512-4b5e-4b07-9d74-ef0f796d2a01

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
import Theorems.Thm_FirstPassageLinearTransport_rawTime_prefix_cases
import Theorems.Thm_FirstPassageLinearTransport_rawLogDeviation_intermediate
import Theorems.Thm_FirstPassageLinearTransport_abs_rawLogDeviation_rawTime_le
import Theorems.Thm_FirstPassageLinearTransport_a0_pos
import Theorems.Thm_FirstPassageLinearTransport_driftGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {n k : ℕ} {E F : ℝ}
    (hn : 0 < n)
    (hshortcut : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E)
    (hodd : ∀ j : ℕ, j ≤ k →
      |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    ∀ i : ℕ, i ≤ rawTime n k →
      |rawLogDeviation n i| ≤
        E + rawOddDeviationCoefficient * F + Real.log 2 := by
  intro i hi
  rcases rawTime_prefix_cases hi with ⟨j, hjk, hj⟩
  have hcorresponding (j : ℕ) (hjk : j ≤ k) :
      |rawLogDeviation n (rawTime n j)| ≤
        E + rawOddDeviationCoefficient * F :=
    abs_rawLogDeviation_rawTime_le (hshortcut j hjk) (hodd j hjk)
  rcases hj with htime | hintermediate
  · subst i
    have hlogTwo0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    linarith [hcorresponding j hjk]
  · rcases hintermediate with ⟨hjkStrict, hoddState, htime⟩
    subst i
    have hjNext : j + 1 ≤ k := by omega
    have hnext := hcorresponding (j + 1) hjNext
    have hinter := rawLogDeviation_intermediate hn hoddState
    have hgap0 := driftGap_pos
    have hgap1 : driftGap < 1 := by
      unfold driftGap
      linarith [a0_pos]
    have hlogTwo0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcorr0 : 0 ≤ (1 - 2 * driftGap / 3) * Real.log 2 := by
      exact mul_nonneg (by nlinarith) hlogTwo0.le
    have hcorrLe : (1 - 2 * driftGap / 3) * Real.log 2 ≤
        Real.log 2 := by
      nlinarith
    have habs := abs_add_le (rawLogDeviation n (rawTime n (j + 1)))
      ((1 - 2 * driftGap / 3) * Real.log 2)
    rw [← hinter, abs_of_nonneg hcorr0] at habs
    nlinarith
end FirstPassageLinearTransport
