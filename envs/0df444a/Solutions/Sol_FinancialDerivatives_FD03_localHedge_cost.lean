-- Prove2me | solution 1 for FinancialDerivatives.FD03.localHedge_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:02:19.006381+00:00
-- url     : https://prove2.me/submissions/2c2b0ced-50b3-4d42-b788-003805947d43

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd03_localHedge
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (spot vu vd : ℝ)
    (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * spot +
      (localHedge m spot vu vd).2 = oneStepValue m vu vd := by

  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  have h3 := m.down_pos
  have hud : m.up - m.down ≠ 0 := by linarith
  have hg : m.growth ≠ 0 := by linarith
  unfold localHedge oneStepValue upWeight
  simp only
  field_simp
  ring
