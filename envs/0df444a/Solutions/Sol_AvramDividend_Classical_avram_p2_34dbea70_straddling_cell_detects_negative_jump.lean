-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_straddling_cell_detects_negative_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:07:19.909841+00:00
-- url     : https://prove2.me/submissions/bf4fa112-de82-4a56-8be9-24c2eac99cb4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- A negative càdlàg jump is eventually visible in any sequence of cells
whose left endpoints tend strictly from the left and right endpoints tend
from the right. This is the local analytic part of source grid capture. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (a b : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝[<] u))
    (hb : Tendsto b atTop (nhdsWithin u (Ici u)))
    (hLeft : Tendsto Y (𝓝[<] u)
      (𝓝 (Function.leftLim Y u)))
    (hRight : ContinuousWithinAt Y (Ici u) u)
    (ε : ℝ) (hε : 0 < ε)
    (hJump : Y u - Function.leftLim Y u ≤ -ε) :
    ∀ᶠ n : ℕ in atTop, Y (b n) - Y (a n) < -ε / 2 := by
  have hYL : Tendsto (fun n : ℕ => Y (a n)) atTop
      (𝓝 (Function.leftLim Y u)) := hLeft.comp ha
  have hRightLim : Tendsto Y (nhdsWithin u (Ici u))
      (𝓝 (Y u)) := hRight
  have hYR : Tendsto (fun n : ℕ => Y (b n)) atTop
      (𝓝 (Y u)) := hRightLim.comp hb
  have hDiff : Tendsto (fun n : ℕ => Y (b n) - Y (a n)) atTop
      (𝓝 (Y u - Function.leftLim Y u)) := hYR.sub hYL
  have hStrict : Y u - Function.leftLim Y u < -ε / 2 := by
    linarith
  exact hDiff.eventually (isOpen_Iio.mem_nhds hStrict)
