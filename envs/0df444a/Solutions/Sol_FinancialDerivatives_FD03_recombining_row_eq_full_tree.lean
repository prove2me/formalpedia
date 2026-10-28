-- Prove2me | solution 1 for FinancialDerivatives.FD03.recombining_row_eq_full_tree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:09:10.370181+00:00
-- url     : https://prove2.me/submissions/a60cb132-81e3-404a-8270-d0fa93d149ec

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_rowToRoot
import Definitions.Def_fd03_terminalRow
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket)
    (n : ℕ) (reward : ℝ → ℝ) :
    rowToRoot m n (terminalRow m n reward) =
      europeanValue m n
        (payoffTreeMap reward n (terminalStockTree m n m.initialSpot)) := by
  have step : ∀ (n : ℕ) (row : Fin (n + 2) → ℝ), rowToRoot m (n + 1) row =
      oneStepValue m (rowToRoot m n (fun k => row k.succ)) (rowToRoot m n (fun k => row k.castSucc)) := by
    intro n
    induction n with
    | zero => intro row; rfl
    | succ n ih =>
      intro row
      show rowToRoot m (n + 1) (backwardRow m (n + 1) row) = _
      rw [ih]
      rfl
  have gen : ∀ (n : ℕ) (s : ℝ) (f : ℝ → ℝ),
      rowToRoot m n (fun k => f (s * m.up ^ k.val * m.down ^ (n - k.val))) =
        europeanValue m n (payoffTreeMap f n (terminalStockTree m n s)) := by
    intro n
    induction n with
    | zero => intro s f; show f _ = f s; simp
    | succ n ih =>
      intro s f
      rw [step]
      show _ = oneStepValue m _ _
      rw [← ih (s * m.up) f, ← ih (s * m.down) f]
      congr 2
      · funext k
        congr 1
        simp only [Fin.val_succ, Nat.add_sub_add_right, pow_succ]
        ring
      · funext k
        congr 1
        simp only [Fin.coe_castSucc]
        rw [show n + 1 - k.val = (n - k.val) + 1 by have := k.isLt; omega, pow_succ]
        ring
  exact gen n m.initialSpot reward


