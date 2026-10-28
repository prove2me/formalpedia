-- Prove2me | solution 1 for AvramDividend.Classical.chat04_explicit_shifted_killed_survival_schedule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:02:38.873431+00:00
-- url     : https://prove2.me/submissions/05ce25e2-1a07-47b2-8d81-e43752cad39c

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage

open scoped NNReal
open AvramDividend.Classical

theorem solution (T : ℝ≥0) :
    ∃ τ : ℕ → ℝ≥0,
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ∧
      (∃ j : ℕ, τ j = T) := by
  refine ⟨fun j => Nat.casesOn j T (fun i => ((Nat.unpair i).2 : ℝ≥0) *
      ((((Nat.unpair i).1 + 1 : ℕ) : ℝ≥0)⁻¹)), ?_, ⟨0, rfl⟩⟩
  intro n hn k
  obtain ⟨j, hj⟩ := chat04_nat_pairing_rational_grid_coverage n k hn
  exact ⟨j + 1, hj⟩
