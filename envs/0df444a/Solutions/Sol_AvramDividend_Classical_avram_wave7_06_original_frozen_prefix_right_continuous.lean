-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_frozen_prefix_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:49:04.698851+00:00
-- url     : https://prove2.me/submissions/1ad4c24a-bf2e-4639-80b9-87ad6309a56d

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
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    ∀ u : ℝ≥0,
      ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (min v T) ω) (Ici u) u := by
  intro u
  let f : ℝ≥0 → ℝ≥0 := fun v => min v T
  have hMin : ContinuousWithinAt f (Ici u) u := by
    change ContinuousWithinAt (fun v : ℝ≥0 => min v T) (Ici u) u
    exact (continuous_id.min continuous_const).continuousWithinAt
  have hMaps : Set.MapsTo f (Ici u) (Ici (f u)) := by
    intro v hv
    have huv : u ≤ v := hv
    change min u T ≤ min v T
    exact min_le_min huv le_rfl
  have hComp :
      ContinuousWithinAt
        ((fun s : ℝ≥0 => X.X s ω) ∘ f) (Ici u) u :=
    (X.rightCont ω (f u)).comp hMin hMaps
  simpa only [f, Function.comp_def] using hComp
