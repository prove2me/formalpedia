-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_leftlimit_threshold_tendsto_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:49:03.103209+00:00
-- url     : https://prove2.me/submissions/f2e36a1c-4a9c-4749-8f9a-83787a12bd4a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- At positive time a left-hand limit witness is the intrinsic leftLim. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + 1 / ((n : ℝ) + 1) ≤ l) ↔
    (∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l)) ∧
    X.X t ω + 1 / ((n : ℝ) + 1) ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by
  classical
  let f : ℝ≥0 → ℝ := fun s => X.X s ω
  haveI : (nhdsWithin t (Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  change (∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l) ∧
      f t + 1 / ((n : ℝ) + 1) ≤ l) ↔
    (∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) ∧
      f t + 1 / ((n : ℝ) + 1) ≤ Function.leftLim f t
  constructor
  · rintro ⟨l, hl, hle⟩
    have hLeft : Tendsto f (nhdsWithin t (Iio t))
        (nhds (Function.leftLim f t)) :=
      tendsto_leftLim_of_tendsto ⟨l, hl⟩
    have heq : l = Function.leftLim f t :=
      tendsto_nhds_unique hl hLeft
    refine ⟨⟨l, hl⟩, ?_⟩
    rwa [← heq]
  · rintro ⟨⟨l, hl⟩, hle⟩
    exact ⟨Function.leftLim f t,
      tendsto_leftLim_of_tendsto ⟨l, hl⟩, hle⟩
