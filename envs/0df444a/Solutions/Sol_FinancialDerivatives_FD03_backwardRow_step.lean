-- Prove2me | solution 1 for FinancialDerivatives.FD03.backwardRow_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:02:14.827805+00:00
-- url     : https://prove2.me/submissions/e92bf863-ed91-4569-9d60-620bfb097f28

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_backwardRow
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (t : ℕ)
    (next : Fin (t + 2) → ℝ) (k : Fin (t + 1)) :
    backwardRow m t next k =
      oneStepValue m (next (Fin.succ k)) (next (Fin.castSucc k)) := by

  rfl
