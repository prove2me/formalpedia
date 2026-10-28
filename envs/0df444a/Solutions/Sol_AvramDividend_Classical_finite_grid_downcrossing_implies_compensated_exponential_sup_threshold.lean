-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_downcrossing_implies_compensated_exponential_sup_threshold
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:47:49.478999+00:00
-- url     : https://prove2.me/submissions/bfd087cf-946f-4de4-b2fe-5868d62aee8c

import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

theorem solution
    (g : ℕ → NNReal) (y : ℕ → ℝ)
    (ε κ b : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (n k : ℕ) (hk : k ≤ n) (hdown : y k ≤ -b) :
    Real.exp (ε * b) ≤
      (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one
        (fun i => Real.exp (-ε * y i + κ * (g i : ℝ))) := by
  refine le_trans ?_ (Finset.le_sup' (fun i => Real.exp (-ε * y i + κ * (g i : ℝ)))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ κ * (g k : ℝ) := mul_nonneg hκ (g k).2
  nlinarith
