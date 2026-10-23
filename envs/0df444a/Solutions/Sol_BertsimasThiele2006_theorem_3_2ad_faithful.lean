-- Prove2me | solution 1 for BertsimasThiele2006.theorem_3_2ad_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:39:16.307496+00:00
-- url     : https://prove2.me/submissions/ff34c551-6e18-40d5-8b30-c4d44b539d18

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Theorems.Thm_RobustInventory_SingleStation_theorem_3_2

open Finset RobustInventory.SingleStation

theorem solution (M : Model)
    (hdem : ∀ k, M.what k ≤ M.wbar k) :
    (∀ u : ℕ → ℝ,
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r) ↔
        M.IsNominalOptimal M.wmod u) ∧
    (∀ (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (u' : ℕ → ℝ),
      M.IsRobustOptimal u y q r → M.IsNominalOptimal M.wmod u' →
        M.robustObjective u y =
          M.nominalCost M.wmod u' + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k) := by
  obtain ⟨-, ha, hd, -⟩ := theorem_3_2 M
  exact ⟨ha, hd⟩
