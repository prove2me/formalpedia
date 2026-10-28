-- Prove2me | solution 1 for FinancialDerivatives.FD02.FD01_price_eq_riskNeutralValue
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:12:07.309956+00:00
-- url     : https://prove2.me/submissions/c2189c4d-408d-4a33-b72b-fc8484d0eebc

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

theorem solution (m : TwoStateMarket) (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1) (H : Bool → ℝ) :
  (toFD01PriceSystem m hq0 hq1).price H = riskNeutralValue m H := by
  have hg := m.growth_pos
  simp only [FinancialDerivatives.FD01.FinitePriceSystem.price, toFD01PriceSystem, Fintype.sum_bool,
    riskNeutralValue]
  field_simp
