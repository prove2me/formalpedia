-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_shifted_future_source_leftLim_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:30:13.658417+00:00
-- url     : https://prove2.me/submissions/3d558351-eb55-4305-903b-7babe00c068d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Strict-left limits of the actual shifted increment path are translated
strict-left limits of the same original source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s u : ℝ≥0) (hu : 0 < u) :
    Function.leftLim
      (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u =
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) (s + u) -
        X.X s ω := by
  have hpos : 0 < s + u :=
    add_pos_of_nonneg_of_pos (zero_le : (0 : ℝ≥0) ≤ s) hu
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
  have hleft :
      Tendsto (fun v : ℝ≥0 => X.X v ω) (𝓝[<] (s + u))
        (𝓝 (Function.leftLim (fun v : ℝ≥0 => X.X v ω) (s + u))) :=
    tendsto_leftLim_of_tendsto (X.leftLim ω (s + u) hpos)
  have htrans := hleft.comp hadd
  have hsub :
      Tendsto (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
        (𝓝[<] u)
        (𝓝 (Function.leftLim (fun v : ℝ≥0 => X.X v ω) (s + u) -
          X.X s ω)) := by
    simpa [Function.comp_def] using htrans.sub tendsto_const_nhds
  haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  exact leftLim_eq_of_tendsto hsub
