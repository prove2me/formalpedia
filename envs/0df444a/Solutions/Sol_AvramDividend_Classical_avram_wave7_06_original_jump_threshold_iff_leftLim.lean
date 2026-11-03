-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_jump_threshold_iff_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:59:31.542204+00:00
-- url     : https://prove2.me/submissions/cb6802cb-eac0-4839-abf7-55da65d71e8d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + 1 / ((n : ℝ) + 1) ≤ l) ↔
    X.X t ω + 1 / ((n : ℝ) + 1) ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
  classical
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have heq : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = l :=
    leftLim_eq_of_tendsto hl
  constructor
  · rintro ⟨u, hu, hle⟩
    have hUnique : u = l := tendsto_nhds_unique hu hl
    rw [heq, ← hUnique]
    exact hle
  · intro h
    refine ⟨l, hl, ?_⟩
    rwa [heq] at h
