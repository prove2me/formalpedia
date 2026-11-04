-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_intrinsic_nonnegative_mark_simple_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:32:16.366413+00:00
-- url     : https://prove2.me/submissions/658a7de9-dd0c-486b-be65-b52d10cf9465

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A finite nonnegative mark-simple jump integral is exactly the finite
weighted sum of true original-path marked-jump counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (c : ι → ℝ≥0∞) (ω : Ω) :
    (∫⁻ p : ℝ≥0 × ℝ,
      ∑ i ∈ S, (Ioc s t ×ˢ B i).indicator (fun _ => c i) p
      ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ i ∈ S, c i *
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i) := by
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change (∫⁻ p, ∑ i ∈ S,
    (Ioc s t ×ˢ B i).indicator (fun _ => c i) p ∂N) =
      ∑ i ∈ S, c i * N (Ioc s t ×ˢ B i)
  have hm (i : ι) (hi : i ∈ S) :
      Measurable (fun p : ℝ≥0 × ℝ =>
        (Ioc s t ×ˢ B i).indicator (fun _ => c i) p) :=
    measurable_const.indicator (measurableSet_Ioc.prod (hB i hi))
  rw [lintegral_finset_sum S hm]
  apply Finset.sum_congr rfl
  intro i hi
  exact lintegral_indicator_const
    (measurableSet_Ioc.prod (hB i hi)) (c i)
