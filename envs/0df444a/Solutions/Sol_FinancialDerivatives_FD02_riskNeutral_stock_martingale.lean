-- Prove2me | solution 1 for FinancialDerivatives.FD02.riskNeutral_stock_martingale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:07:03.875556+00:00
-- url     : https://prove2.me/submissions/2f2656fe-15d4-4d9a-85ec-8ee57962dd54

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) :
  riskNeutralUp m * m.up + (1 - riskNeutralUp m) * m.down = m.growth := by
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  unfold riskNeutralUp
  field_simp
  ring
