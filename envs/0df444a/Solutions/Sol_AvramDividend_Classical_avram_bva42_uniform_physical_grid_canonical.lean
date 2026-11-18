-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva42_uniform_physical_grid_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:02:21.901372+00:00
-- url     : https://prove2.me/submissions/938f7c12-bca2-43ea-9d26-41d5e0d9e3d9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0 ∧
        ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, u n i ≤ u n (i + 1)) ∧
      (∀ n i, (u n i : ℝ) =
        T * (i : ℝ) / ((n : ℝ) + 2)) := by
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  have huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2) := by
    intro n i
    rfl
  have hu : ∀ n i, u n i ≤ u n (i + 1) := by
    intro n i
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    gcongr
    exact_mod_cast Nat.le_succ i
  have hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)) := by
    intro n
    constructor
    · apply Subtype.ext
      simp [u]
    · change T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) =
        T - T / ((n : ℝ) + 2)
      push_cast
      have hn : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
  exact ⟨u, hgrid, hu, huniform⟩
