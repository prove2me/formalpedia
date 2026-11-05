-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_jump_removed_uniform_positive_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:36:46.784933+00:00
-- url     : https://prove2.me/submissions/8a3f4b47-79e0-48c3-a56a-34cfb420b1e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine original Lévy motion with its left jumps removed has a uniform
modulus on each compact positive-time interval. The actual continuous
nonnegative source residual is retained and may be nonzero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ≥0, 0 < a →
      UniformContinuousOn (fun s : ℝ≥0 => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) (Icc a b) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time X hBV]
    with ω hω
  intro a b ha
  apply isCompact_Icc.uniformContinuousOn_of_continuous
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le ha ht.1
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
  exact (hlinear.sub (hω t htpos)).continuousWithinAt
