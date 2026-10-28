-- Prove2me | solution 1 for FinancialDerivatives.FD02.statePrices_bank_calibration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:09:38.319368+00:00
-- url     : https://prove2.me/submissions/1cb932ab-32c1-4a4b-a6a3-6753c99bfb04

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
  (toFD01PriceSystem m hq0 hq1).price (fun _ : Bool => m.growth) = 1 := by
  have hg := m.growth_pos
  simp only [FinancialDerivatives.FD01.FinitePriceSystem.price, toFD01PriceSystem, Fintype.sum_bool]
  field_simp
  ring
