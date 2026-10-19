-- Prove2me | solution 1 for CohnElkies.unitBallVolume_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/6372cf5a-7738-4328-ab27-3f2ed348ac06

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Metric
open scoped ENNReal
namespace CohnElkies
theorem _root_.solution (k : ℕ) :
    unitBallVolume (2 * k) = Real.pi ^ k / (k.factorial : ℝ) := by
  unfold unitBallVolume
  have hhalf : ((↑(2 * k) : ℝ) / 2) = (k : ℝ) := by
    push_cast
    ring
  rw [hhalf, Real.rpow_natCast, Real.Gamma_nat_eq_factorial]
end CohnElkies
