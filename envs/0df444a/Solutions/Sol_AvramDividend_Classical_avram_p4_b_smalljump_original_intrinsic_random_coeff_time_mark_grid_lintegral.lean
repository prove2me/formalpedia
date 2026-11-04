-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_random_coeff_time_mark_grid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:51:50.274855+00:00
-- url     : https://prove2.me/submissions/6da47f1b-a461-4a5d-8e4e-eeff1e122e2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A finite random nonnegative predictable-simple kernel on arbitrary
physical time-mark rectangles integrates against the same original Lévy
intrinsic marked measure as its weighted original-path marked count sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc (s i) (t i) ×ˢ B i).indicator
        (fun _ => H i ω) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ i ∈ S, H i ω *
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) := by
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change (∫⁻ p, ∑ i ∈ S,
    (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p ∂N) =
      ∑ i ∈ S, H i ω * N (Ioc (s i) (t i) ×ˢ B i)
  have hm (i : ι) (hi : i ∈ S) : Measurable
      (fun p : ℝ≥0 × ℝ =>
        (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p) :=
    measurable_const.indicator (measurableSet_Ioc.prod (hB i hi))
  rw [lintegral_finset_sum S hm]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_const
    (measurableSet_Ioc.prod (hB i hi)) (H i ω)
