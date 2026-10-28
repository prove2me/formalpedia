-- Prove2me | solution 1 for FinancialDerivatives.FD03.hedgeShiftBank_wealth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:07:40.227499+00:00
-- url     : https://prove2.me/submissions/39182a5a-d841-4ea4-ae1a-4081839bcdad

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_hedgeShiftBank
import Definitions.Def_fd03_hedgeWealth
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03


open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (spot extra : ℝ) (h : HedgeTree n) :
    hedgeWealth m n spot (hedgeShiftBank m n extra h) =
      hedgeWealth m n spot h + extra := by


  induction n generalizing spot extra with
  | zero =>
    cases h with
    | terminal cash => rfl
  | succ n ih =>
    cases h with
    | node shares bank up down =>
      show shares * spot + (bank + extra) = shares * spot + bank + extra
      ring
