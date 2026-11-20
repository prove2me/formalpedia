-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_cap_tube_below_barrier_implies_upper_exit_clock_after_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:46:06.304166+00:00
-- url     : https://prove2.me/submissions/65478151-394d-4244-91d6-37c7413f697d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ω : Ω) (u σ : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hBound : ∀ s : ℝ≥0, s ≤ σ → X.X s ω ≤ a - x) :
    σ ≤ u := by
  have hInf : (σ : ℝ≥0∞) ≤ (u : ℝ≥0∞) := by
    rw [hu]
    refine le_iInf fun s => le_iInf fun hs => ?_
    have hlt : σ < s := by
      by_contra hnot
      have hsσ : s ≤ σ := le_of_not_gt hnot
      exact (not_lt_of_ge (hBound s hsσ)) hs
    exact_mod_cast (le_of_lt hlt)
  exact_mod_cast hInf
