-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_zero_barrier_candidate_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:37:04.277007+00:00
-- url     : https://prove2.me/submissions/247ea863-dd51-4d69-9554-74763088b958

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_zero_barrier_candidate_eq_posPart
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The unbounded-variation zero-barrier candidate has global Lipschitz
constant one, including across the killed boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    LipschitzWith (1 : ℝ≥0) (barrierValue W 0) := by
  have heq : barrierValue W 0 = fun x : ℝ => max x 0 := by
    funext x
    exact unbounded_variation_zero_barrier_candidate_eq_posPart
      X q hq W hW hnbv x
  rw [heq]
  have hid : LipschitzWith (1 : ℝ≥0) (fun x : ℝ => x) :=
    LipschitzWith.id
  exact hid.max_const 0
