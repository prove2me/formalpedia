-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_grid_exit_upper_side_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:42:54.516219+00:00
-- url     : https://prove2.me/submissions/fdd7ce5f-acff-488e-acbf-b74021a0d499

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_exit_before_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Strict upper-exit side is preserved on the first sufficiently fine grid
exit when the lower boundary is not crossed before an intervening horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ N : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτN : τ < N)
    (hNoLower : ∀ s : ℝ≥0, s < N → lower ≤ X.X s ω) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < N ∧
        upper < X.X ((k : ℝ≥0) * h) ω ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_first_grid_exit_before_horizon
      X ω lower upper τ N hτ hτN
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨k, hτk, hkN, hkExit, hkfirst⟩ := hmesh h hh hhd
  have hUp : upper < X.X ((k : ℝ≥0) * h) ω := by
    rcases hkExit with hDown | hUp
    · exact False.elim ((not_lt_of_ge
        (hNoLower ((k : ℝ≥0) * h) hkN)) hDown)
    · exact hUp
  exact ⟨k, hτk, hkN, hUp, hkfirst⟩