-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_count_union_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:42:03.485233+00:00
-- url     : https://prove2.me/submissions/8750f634-dbbf-4c1e-9f79-34b16c52307c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source marked counts are subadditive under arbitrary unions of mark sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B C : Set ℝ) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX ω (Ioc 0 T ×ˢ (B ∪ C)) ≤
     NX ω (Ioc 0 T ×ˢ B) + NX ω (Ioc 0 T ×ˢ C)) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change NX ω (Ioc 0 T ×ˢ (B ∪ C)) ≤
    NX ω (Ioc 0 T ×ˢ B) + NX ω (Ioc 0 T ×ˢ C)
  rw [Set.prod_union]
  exact measure_union_le _ _
