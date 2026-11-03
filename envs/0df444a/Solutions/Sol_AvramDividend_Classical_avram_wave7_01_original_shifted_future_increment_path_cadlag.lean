-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_shifted_future_increment_path_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:46:52.205325+00:00
-- url     : https://prove2.me/submissions/624d507c-ccc8-4599-8dea-1208ed598a07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0) :
    (∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
        (Ici t) t) ∧
    (∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto
        (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
        (𝓝[<] u) (𝓝 l)) := by
  constructor
  · exact shiftedLevy_increments_right_continuous X ω s
  · intro u hu
    have hpos : 0 < s + u :=
      add_pos_of_nonneg_of_pos (zero_le : (0 : ℝ≥0) ≤ s) hu
    rcases X.leftLim ω (s + u) hpos with ⟨l, hl⟩
    have hident :
        Tendsto (fun v : ℝ≥0 => v) (𝓝[<] u) (𝓝 u) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have haddNhd :
        Tendsto (fun v : ℝ≥0 => s + v) (𝓝[<] u)
          (𝓝 (s + u)) := tendsto_const_nhds.add hident
    have hadd :
        Tendsto (fun v : ℝ≥0 => s + v) (𝓝[<] u)
          (𝓝[<] (s + u)) := by
      apply (tendsto_nhdsWithin_iff).2
      refine ⟨haddNhd, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      simpa only [Set.mem_Iio, add_comm s] using (add_lt_add_left hv s)
    refine ⟨l - X.X s ω, ?_⟩
    have hshift := hl.comp hadd
    simpa [Function.comp_def] using hshift.sub tendsto_const_nhds
