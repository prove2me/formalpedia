-- Prove2me | solution 1 for FinancialDerivatives.FD03.hedgeShiftBank_selfFinancing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:09:31.149745+00:00
-- url     : https://prove2.me/submissions/282af5a3-7e10-4544-b882-4047f265eeee

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_hedgeShiftBank
import Definitions.Def_fd03_SelfFinancing
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
import Definitions.Def_fd03_hedgeWealth
open FinancialDerivatives.FD03

theorem S200F_w (m : BinomialMarket) (n : ℕ)
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

open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket)
    (n : ℕ) (spot extra : ℝ) (h : HedgeTree n)
    (hsf : SelfFinancing m n spot h) :
    SelfFinancing m n spot (hedgeShiftBank m n extra h) := by


  induction n generalizing spot extra with
  | zero =>
    cases h with
    | terminal cash => trivial
  | succ n ih =>
    cases h with
    | node shares bank up down =>
      obtain ⟨e1, e2, s1, s2⟩ := hsf
      refine ⟨?_, ?_, ih _ _ _ s1, ih _ _ _ s2⟩
      · show shares * (spot * m.up) + (bank + extra) * m.growth =
          hedgeWealth m n (spot * m.up) (hedgeShiftBank m n (extra * m.growth) up)
        rw [S200F_w]; linarith
      · show shares * (spot * m.down) + (bank + extra) * m.growth =
          hedgeWealth m n (spot * m.down) (hedgeShiftBank m n (extra * m.growth) down)
        rw [S200F_w]; linarith
