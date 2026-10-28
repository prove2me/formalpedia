-- Prove2me | solution 1 for FinancialDerivatives.FD02.statePrices_sum_discount
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:08:52.553449+00:00
-- url     : https://prove2.me/submissions/1e0301c3-c488-4752-b99d-bcb2bc0cefba

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Mathlib.Tactic

open FinancialDerivatives.FD02

theorem solution (m : TwoStateMarket) :
  riskNeutralUp m / m.growth + (1 - riskNeutralUp m) / m.growth = 1 / m.growth := by
  rw [← add_div]; ring_nf
