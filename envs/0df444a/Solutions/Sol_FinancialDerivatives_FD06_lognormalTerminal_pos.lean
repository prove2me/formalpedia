-- Prove2me | solution 1 for FinancialDerivatives.FD06.lognormalTerminal_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:07:14.138168+00:00
-- url     : https://prove2.me/submissions/6bd4f1e9-f78b-486f-b2b0-170f02322b04

import Mathlib
import Definitions.Def_fd06_lognormalTerminal

open FinancialDerivatives.FD06

theorem solution (S R Q V z : ℝ) (hS : 0 < S) : 0 < lognormalTerminal S R Q V z := by
  unfold lognormalTerminal; positivity
