-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_ae_marked_Y_cells_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:53:07.001165+00:00
-- url     : https://prove2.me/submissions/1b6e372a-ba3b-4825-9851-530db179cb3f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_removed_continuous_positive_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (S : Finset ℝ≥0) (hPositive : ∀ t ∈ S, 0 < t)
        (left right : ℕ → ℝ≥0 → ℝ≥0)
        (hLeft : ∀ t ∈ S,
          Filter.Tendsto (fun k => left k t) Filter.atTop (nhds t))
        (hRight : ∀ t ∈ S,
          Filter.Tendsto (fun k => right k t) Filter.atTop (nhds t)),
      let Y : ℝ≥0 → ℝ := fun s => X.X s ω +
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)
      Filter.Tendsto
        (fun k => ∑ t ∈ S, |Y (right k t) - Y (left k t)|)
        Filter.atTop (nhds 0) := by
  filter_upwards
    [avram_p3_main_original_jump_removed_continuous_positive_time X hBV]
    with ω hcont
  intro S hPositive left right hLeft hRight Y
  apply avram_p3_d_bvmesh_finitely_marked_original_jump_cells_vanish
    S (fun k t => Y (right k t) - Y (left k t))
  intro t ht
  have hY : ContinuousAt Y t := hcont t (hPositive t ht)
  have hL : Filter.Tendsto
      (fun k => Y (left k t)) Filter.atTop (nhds (Y t)) :=
    hY.tendsto.comp (hLeft t ht)
  have hR : Filter.Tendsto
      (fun k => Y (right k t)) Filter.atTop (nhds (Y t)) :=
    hY.tendsto.comp (hRight t ht)
  simpa only [sub_self] using hR.sub hL
