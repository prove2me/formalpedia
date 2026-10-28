-- Prove2me | solution 1 for FinancialDerivatives.FD02.riskNeutral_martingale_unique_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:08:21.262752+00:00
-- url     : https://prove2.me/submissions/edc9af1f-a91e-4a97-9d55-9838fdad8693

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (w : ℝ) (h : w * m.up + (1 - w) * m.down = m.growth) :
  w = riskNeutralUp m := by
  have hpos : 0 < m.up - m.down := by linarith [m.down_lt_up]
  unfold riskNeutralUp
  rw [eq_div_iff hpos.ne']
  linarith
