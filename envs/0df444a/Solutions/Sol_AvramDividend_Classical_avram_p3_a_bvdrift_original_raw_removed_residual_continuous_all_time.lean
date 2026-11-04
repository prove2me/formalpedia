-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_continuous_all_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:02:33.938669+00:00
-- url     : https://prove2.me/submissions/066d3ad6-1c7d-4b42-93e6-70f46fd42d02

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source's raw-jump-removed residual is continuous even at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 =>
      (((t : ℝ) * X.drift - X.X t ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_removed_residual_continuous_positive_time X hBV,
     avram_p3_a_bvdrift_original_raw_removed_residual_right_continuous X hBV]
    with ω hpos hright
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    have hIci : Set.Ici (0 : ℝ≥0) = Set.univ := by
      ext x
      simp [zero_le]
    have hsplit : (𝓝 (0 : ℝ≥0)) =
        (𝓝[>] (0 : ℝ≥0)) ⊔ (𝓝[{(0 : ℝ≥0)}] (0 : ℝ≥0)) := by
      simpa [nhdsGE, hIci] using
        (nhdsGT_sup_nhdsWithin_singleton (0 : ℝ≥0)).symm
    let f : ℝ≥0 → ℝ := fun s =>
      (((s : ℝ) * X.drift - X.X s ω) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
    change Filter.map f (𝓝 (0 : ℝ≥0)) ≤ 𝓝 (f 0)
    rw [hsplit, Filter.map_sup]
    apply sup_le
    · exact hright 0
    · have hpure : Filter.Tendsto f (pure (0 : ℝ≥0)) (𝓝 (f 0)) :=
        tendsto_pure_nhds f (0 : ℝ≥0)
      simpa [Filter.Tendsto, nhdsWithin_singleton] using hpure
  · exact hpos t (pos_iff_ne_zero.mpr ht)
