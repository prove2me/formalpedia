-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_grid_capped_time_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:43:15.617935+00:00
-- url     : https://prove2.me/submissions/7c3047f1-a410-4100-ba93-3c377074b046

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Capping the first strict grid exit at a horizon preserves its convergence
from above to the capped continuous strict-exit infimum, regardless of
whether the continuous infimum precedes, equals or exceeds that horizon.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) ∧
        min τ T ≤ min ((k : ℝ≥0) * h) T ∧
        min ((k : ℝ≥0) * h) T < min τ T + ε := by
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_first_grid_strict_exit_approaches_infimum
      X ω lower upper τ hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨k, hτk, hkε, hkExit, hkfirst⟩ := hmesh h hh hhd
  refine ⟨k, hkExit, hkfirst, ?_, ?_⟩
  · apply le_min
    · exact (min_le_left τ T).trans hτk
    · exact min_le_right τ T
  · by_cases hτT : τ ≤ T
    · rw [min_eq_left hτT]
      exact (min_le_left ((k : ℝ≥0) * h) T).trans_lt hkε
    · have hTτ : T ≤ τ := le_of_not_ge hτT
      rw [min_eq_right hTτ]
      exact (min_le_right ((k : ℝ≥0) * h) T).trans_lt
        (lt_add_of_pos_right T hε)
