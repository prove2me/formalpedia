-- Prove2me | solution 1 for FinancialDerivatives.FD03.snell_maturity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:59:57.735826+00:00
-- url     : https://prove2.me/submissions/afaa1d38-ff46-4ca2-935b-9c93cd9ab168

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (c : ℝ) :
    snellValue m 0 (.maturity c) = c := by
  rfl

