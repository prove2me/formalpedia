-- Prove2me | solution 1 for AvramDividend.Classical.stopped_renewal_geometric_scale_ratio_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:57:21.218988+00:00
-- url     : https://prove2.me/submissions/342926f3-33d8-40d5-a22e-baab98c17729

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Convert a forward first-record scale ratio into its geometric renewal reward. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (W : ℝ → ℝ) (a ε : ℝ)
    (hWa : W (a + ε) ≠ 0)
    (hgap : W (a + ε) - W a ≠ 0) :
    ε / (1 - W a / W (a + ε)) =
      ε * W (a + ε) / (W (a + ε) - W a) := by
  have hden : 1 - W a / W (a + ε) =
      (W (a + ε) - W a) / W (a + ε) := by
    field_simp
  rw [hden]
  field_simp
