-- Prove2me | solution 1 for BianchiIX.radial_arrival_factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:53:36.846171+00:00
-- url     : https://prove2.me/submissions/ed22c385-4772-46f7-b3b9-03f6c47823dc

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {r c f : ℝ} (hr : 0 < r) (hc : c ≤ -1 / 2) (hf : f ≤ 0) :
    c + f / r < 0 ∧ 0 < c / (c + f / r) ∧ c / (c + f / r) ≤ 1 ∧
      |c / (c + f / r) - 1| ≤ 2 * |f| / r := by
  have ha : f / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hf hr.le
  have hc0 : c < 0 := by linarith only [hc]
  have hd : c + f / r < 0 := by linarith only [hc0, ha]
  have hden : (1 / 2 : ℝ) ≤ |c + f / r| := by
    rw [abs_of_neg hd]
    linarith only [hc, ha]
  refine ⟨hd, div_pos_of_neg_of_neg hc0 hd, (div_le_iff_of_neg hd).mpr ?_, ?_⟩
  · linarith only [ha]
  · have hsum : c / (c + f / r) + (f / r) / (c + f / r) = 1 := by
      rw [← add_div, div_self (ne_of_lt hd)]
    have hid : c / (c + f / r) - 1 = -((f / r) / (c + f / r)) := by linarith only [hsum]
    rw [hid, abs_neg, abs_div, abs_div, abs_of_pos hr]
    calc
      _ ≤ (|f| / r) / (1 / 2) := div_le_div_of_nonneg_left
        (div_nonneg (abs_nonneg _) hr.le) (by norm_num) hden
      _ = 2 * |f| / r := by ring
