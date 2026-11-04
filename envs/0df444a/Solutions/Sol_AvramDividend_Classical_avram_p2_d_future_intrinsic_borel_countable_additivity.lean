-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_intrinsic_borel_countable_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:28.91584+00:00
-- url     : https://prove2.me/submissions/4d54caea-dca4-4506-bd33-97e245007c9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The exact original intrinsic marked sample count is countably additive on
pairwise-disjoint Borel time-mark regions, allowing infinite activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (C : ℕ → Set (ℝ≥0 × ℝ))
    (hDisj : Pairwise (Function.onFun Disjoint C))
    (hC : ∀ n, MeasurableSet (C n)) :
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (⋃ n, C n) =
      ∑' n, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (C n) := by
  exact MeasureTheory.measure_iUnion hDisj hC
