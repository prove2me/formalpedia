-- Prove2me | solution 1 for FinancialDerivatives.FD02.statePrices_stock_calibration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:09:38.285368+00:00
-- url     : https://prove2.me/submissions/9b57219a-916c-4d7d-8108-a01266453cf5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1) :
  (toFD01PriceSystem m hq0 hq1).price (fun ω : Bool => if ω then m.spot * m.up else m.spot * m.down) = m.spot := by
  have hg := m.growth_pos
  have h : m.up - m.down ≠ 0 := by linarith [m.down_lt_up]
  simp only [FinancialDerivatives.FD01.FinitePriceSystem.price, toFD01PriceSystem, Fintype.sum_bool,
    if_true, if_false, Bool.false_eq_true]
  unfold riskNeutralUp
  field_simp
  ring
