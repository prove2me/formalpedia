-- Prove2me | solution 1 for AvramDividend.Classical.stopped_renewal_geometric_scale_ratio_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:57:15.943468+00:00
-- url     : https://prove2.me/submissions/ffa273c4-ac9b-42f6-95c0-1547f2fa7a8a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Convert a backward first-record scale ratio into its geometric renewal reward. -/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (W : ℝ → ℝ) (a ε : ℝ)
    (hWa : W a ≠ 0)
    (hgap : W a - W (a - ε) ≠ 0) :
    ε * (W (a - ε) / W a) /
        (1 - W (a - ε) / W a) =
      ε * W (a - ε) / (W a - W (a - ε)) := by
  have hden : 1 - W (a - ε) / W a =
      (W a - W (a - ε)) / W a := by
    field_simp
  rw [hden]
  field_simp
