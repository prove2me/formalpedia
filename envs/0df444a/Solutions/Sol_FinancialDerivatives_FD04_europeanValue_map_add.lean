-- Prove2me | solution 1 for FinancialDerivatives.FD04.europeanValue_map_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T10:53:04.69295+00:00
-- url     : https://prove2.me/submissions/15f824dc-11d0-4d6e-a776-ff04aa724792

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
open FinancialDerivatives.FD03

theorem solution (m : BinomialMarket) (n : ℕ)
    (tree : PayoffTree n) (f g : ℝ → ℝ) :
    europeanValue m n (payoffTreeMap (fun x => f x + g x) n tree) =
      europeanValue m n (payoffTreeMap f n tree) +
      europeanValue m n (payoffTreeMap g n tree) := by
  induction n with
  | zero => cases tree; rfl
  | succ n ih =>
    cases tree with
    | branch up down =>
      simp only [payoffTreeMap, europeanValue, ih]
      unfold oneStepValue; ring


