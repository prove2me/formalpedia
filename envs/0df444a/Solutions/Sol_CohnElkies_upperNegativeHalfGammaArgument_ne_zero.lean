-- Prove2me | solution 1 for CohnElkies.upperNegativeHalfGammaArgument_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/9e681828-91c2-40a3-95a7-6d600540d51a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument N s ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [upperNegativeHalfGammaArgument] at hre
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith
end CohnElkies
