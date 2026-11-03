-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_leftLim_before_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:33:42.84478+00:00
-- url     : https://prove2.me/submissions/8217d0e7-cb42-410e-acb9-1c92d5c489c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T u : ℝ≥0) (hu : 0 < u) (huT : u ≤ T) :
    Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u =
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by
  classical
  obtain ⟨l, hl⟩ := X.leftLim ω u hu
  letI : (𝓝[<] u).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  have hBefore :
      (fun v : ℝ≥0 => X.X (min v T) ω) =ᶠ[𝓝[<] u]
        (fun v : ℝ≥0 => X.X v ω) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hvT : v ≤ T := le_trans (le_of_lt hv) huT
    simp only [min_eq_left hvT]
  have hStopped :
      Tendsto (fun v : ℝ≥0 => X.X (min v T) ω)
        (𝓝[<] u) (𝓝 l) := hl.congr' hBefore.symm
  calc
    Function.leftLim (fun v : ℝ≥0 => X.X (min v T) ω) u = l :=
      leftLim_eq_of_tendsto hStopped
    _ = Function.leftLim (fun v : ℝ≥0 => X.X v ω) u :=
      (leftLim_eq_of_tendsto hl).symm
