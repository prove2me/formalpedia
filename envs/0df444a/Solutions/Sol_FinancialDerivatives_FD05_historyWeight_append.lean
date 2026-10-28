-- Prove2me | solution 1 for FinancialDerivatives.FD05.historyWeight_append
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:38:39.331241+00:00
-- url     : https://prove2.me/submissions/27aa3c42-0a7a-4086-ae14-5acd9d4effb1

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_historyWeight

open FinancialDerivatives.FD03 FinancialDerivatives.FD05

theorem solution (m : BinomialMarket) (xs ys : List Bool) :
    historyWeight m (xs ++ ys) =
      historyWeight m xs * historyWeight m ys := by
  simp [historyWeight, List.prod_append]
