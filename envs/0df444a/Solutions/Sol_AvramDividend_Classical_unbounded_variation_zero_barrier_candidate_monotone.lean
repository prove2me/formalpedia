-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:32:39.036006+00:00
-- url     : https://prove2.me/submissions/7b1ca1a4-d36e-45b1-97dd-030e85e99aca

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Mathlib.Order.Monotone.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The zero-barrier value candidate is nondecreasing throughout the real
reserve line when the Lévy process has unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    Monotone (barrierValue W 0) := by
  intro x y hxy
  rw [unbounded_variation_zero_barrier_candidate_eq_posPart
      X q hq W hW hnbv x,
    unbounded_variation_zero_barrier_candidate_eq_posPart
      X q hq W hW hnbv y]
  exact max_le_max hxy le_rfl
