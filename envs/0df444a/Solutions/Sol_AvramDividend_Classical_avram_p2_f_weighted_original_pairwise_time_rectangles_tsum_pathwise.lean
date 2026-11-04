-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:51:18.002625+00:00
-- url     : https://prove2.me/submissions/20d31c3e-8f68-4de2-a037-1b63ead852c1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Countable additivity of the original Lévy jump measure over
non-overlapping time windows with independently varying Borel marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hTimeDisj : Pairwise (fun i j =>
      Disjoint (Ioc (s i) (t i)) (Ioc (s j) (t j))))
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc (s n) (t n) ×ˢ B n) =
    ∑' n, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s n) (t n) ×ˢ B n) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hRectDisj : Pairwise (fun i j =>
      Disjoint (Ioc (s i) (t i) ×ˢ B i)
        (Ioc (s j) (t j) ×ˢ B j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro z hz1 hz2
    exact (Set.disjoint_left.mp (hTimeDisj hij)) hz1.1 hz2.1
  have hRectMeas (n : ℕ) :
      MeasurableSet (Ioc (s n) (t n) ×ˢ B n) :=
    measurableSet_Ioc.prod (hB n)
  change μ (⋃ n, Ioc (s n) (t n) ×ˢ B n) =
    ∑' n, μ (Ioc (s n) (t n) ×ˢ B n)
  exact measure_iUnion hRectDisj hRectMeas
