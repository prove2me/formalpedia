-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_uniform_physical_stopped_grid_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:19:35.049282+00:00
-- url     : https://prove2.me/submissions/9bccd9a4-b7bc-48e3-8a93-4592e67dfdcf

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The physical grid has a zero start, strict last point and monotone cells. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) := by
  dsimp
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2),
      div_nonneg (mul_nonneg (le_of_lt hT) (Nat.cast_nonneg i)) (by positivity)⟩
  refine ⟨u, ?_, ?_⟩
  · intro n
    constructor
    · apply Subtype.ext
      simp [u]
    · dsimp [u]
      change T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) =
          T - T / ((n : ℝ) + 2)
      have hd : ((n : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  · intro n i _
    change (u n i : ℝ) ≤ (u n (i + 1) : ℝ)
    dsimp [u]
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hT)
    exact_mod_cast Nat.le_succ i
