-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_any_boundary_width_continuous_candidate_weighted_truncated_negative_mark_mean_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:55:25.309684+00:00
-- url     : https://prove2.me/submissions/9a5270b3-19d1-4d0e-a457-a9dfe48f71d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun n =>
      (∫ z in Iio (0 : ℝ), min (ε n) (-z) ∂X.ν) * w (ε n))
      atTop (𝓝 (0 : ℝ)) := by
  have hJ :=
    avram_bva_a22_original_BV_any_spatial_boundary_width_truncated_negative_mark_first_moment_vanish
      X hBV ε hε hεlim
  have hWithin : Tendsto ε atTop (𝓝[Set.Ici (0 : ℝ)] (0 : ℝ)) :=
    (tendsto_nhdsWithin_iff).2
      ⟨hεlim, Filter.Eventually.of_forall
        (fun n => Set.mem_Ici.mpr (le_of_lt (hε n).1))⟩
  have hW : Tendsto (fun n => w (ε n)) atTop (𝓝 (w 0)) :=
    (hw_cont.continuousWithinAt (Set.mem_Ici.mpr le_rfl)).tendsto.comp hWithin
  have hProd := hJ.mul hW
  simpa only [zero_mul] using hProd
