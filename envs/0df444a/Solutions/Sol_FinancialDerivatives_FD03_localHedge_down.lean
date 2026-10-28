-- Prove2me | solution 1 for FinancialDerivatives.FD03.localHedge_down
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:02:23.1086+00:00
-- url     : https://prove2.me/submissions/9ee7df0a-9ec2-4cd6-9f8e-670c45d52f64

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_fd03_localHedge
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (spot vu vd : ℝ)
    (hspot : 0 < spot) :
    (localHedge m spot vu vd).1 * (spot * m.down) +
      (localHedge m spot vu vd).2 * m.growth = vd := by

  have h1 := m.down_lt_growth
  have h2 := m.growth_lt_up
  have h3 := m.down_pos
  have hud : m.up - m.down ≠ 0 := by linarith
  have hg : m.growth ≠ 0 := by linarith
  unfold localHedge
  simp only
  field_simp
  ring
