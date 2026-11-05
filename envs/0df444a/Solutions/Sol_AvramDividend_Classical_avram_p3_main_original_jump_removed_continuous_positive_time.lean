-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_jump_removed_continuous_positive_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:33:08.185876+00:00
-- url     : https://prove2.me/submissions/5d0839fc-31b3-4b23-8cf4-533b28f88660

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original jump-removed source path has continuous positive-time motion
on one P-full event. This is the physical drift minus its genuine continuous
monotone residual, without asserting that the residual vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ContinuousAt (fun s : ℝ≥0 => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) t := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time X hBV]
    with ω hω
  intro t ht
  have hlinear :
      ContinuousAt (fun s : ℝ≥0 => (s : ℝ) * X.drift) t := by
    fun_prop
  have hrewrite :
      (fun s : ℝ≥0 => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) =
      (fun s : ℝ≥0 => (s : ℝ) * X.drift -
        (((s : ℝ) * X.drift - X.X s ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0))) := by
    funext s
    ring
  rw [hrewrite]
  exact hlinear.sub (hω t ht)
