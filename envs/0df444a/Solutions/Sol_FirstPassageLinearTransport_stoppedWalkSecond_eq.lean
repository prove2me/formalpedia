-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedWalkSecond_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:52.763601+00:00
-- url     : https://prove2.me/submissions/b39e2dc2-81a5-4da6-bbbf-429efdcb9f15

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p v : ℝ} (x : Bool → ℝ) (lo hi : ℝ)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v) :
    ∀ r z, stoppedWalkSecond p x lo hi r z =
      z ^ 2 + v * stoppedWalkTime p x lo hi r z := by
  intro r
  induction r with
  | zero => simp [stoppedWalkSecond, stoppedWalkTime]
  | succ r ihr =>
      intro z
      by_cases hstop : z < lo ∨ hi ≤ z
      · simp [stoppedWalkSecond, stoppedWalkTime, hstop]
      · simp only [stoppedWalkSecond, stoppedWalkTime, hstop, if_false, ihr]
        calc
          bernoulliAverage p
              ((z + x false) ^ 2 +
                v * stoppedWalkTime p x lo hi r (z + x false))
              ((z + x true) ^ 2 +
                v * stoppedWalkTime p x lo hi r (z + x true)) =
              z ^ 2 + 2 * z * bernoulliAverage p (x false) (x true) +
                bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) +
                v * bernoulliAverage p
                  (stoppedWalkTime p x lo hi r (z + x false))
                  (stoppedWalkTime p x lo hi r (z + x true)) := by
            unfold bernoulliAverage
            ring
          _ = z ^ 2 + v *
              (1 + bernoulliAverage p
                (stoppedWalkTime p x lo hi r (z + x false))
                (stoppedWalkTime p x lo hi r (z + x true))) := by
            rw [hcenter, hvariance]
            ring
end FirstPassageLinearTransport
