-- Prove2me | solution 1 for FinancialDerivatives.FD03.hedgeShiftBank_covers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:09:26.766629+00:00
-- url     : https://prove2.me/submissions/e0f2c704-7223-4b6e-a007-a6613c999fab

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_hedgeShiftBank
import Definitions.Def_fd03_hedgeCoversExercise
import Mathlib.Tactic
import Definitions.Def_fd03_oneStepValue
open FinancialDerivatives.FD03


open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (spot extra : ℝ) (h : HedgeTree n) (exercise : ExerciseTree n)
    (hextra : 0 ≤ extra)
    (hcover : hedgeCoversExercise m n spot h exercise) :
    hedgeCoversExercise m n spot
      (hedgeShiftBank m n extra h) exercise := by


  induction n generalizing spot extra with
  | zero =>
    cases h with
    | terminal cash =>
      cases exercise with
      | maturity r =>
        show r ≤ cash + extra
        have : r ≤ cash := hcover
        linarith
  | succ n ih =>
    cases h with
    | node shares bank up down =>
      cases exercise with
      | node allowed reward U D =>
        obtain ⟨h0, hu, hd⟩ := hcover
        have hg : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
        refine ⟨fun ha => ?_, ih _ _ _ _ (by positivity) hu, ih _ _ _ _ (by positivity) hd⟩
        have := h0 ha
        show reward ≤ shares * spot + (bank + extra)
        linarith
