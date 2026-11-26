-- Prove2me | solution 1 for FirstPassageLinearTransport.stageCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:14:37.915193+00:00
-- url     : https://prove2.me/submissions/9a39f1c6-b190-455b-94f2-aacc99b6cfb5

import Definitions.Def_FirstPassageLinearTransport_Bootstrap
import Definitions.Def_FirstPassageLinearTransport_Scalar

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter Asymptotics
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {omega : ℝ} (homega : 0 ≤ omega) (M : ℕ) :
    (stageCount omega M : ℝ) ≤ omega * Real.log (M + 4) := by
  unfold stageCount
  apply Nat.floor_le
  have hM4 : (1 : ℝ) ≤ (M : ℝ) + 4 := by
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  exact mul_nonneg homega (Real.log_nonneg hM4)
end FirstPassageLinearTransport
