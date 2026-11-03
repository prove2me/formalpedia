-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_random_stopped_marked_interval_pathwise_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:11:14.364645+00:00
-- url     : https://prove2.me/submissions/68fcd786-805a-4f64-b055-2e24b2201d58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked-jump counting measure adds over sample-dependent adjacent intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : Ω → ℝ≥0)
    (hst : ∀ ω, s ω ≤ t ω) (htu : ∀ ω, t ω ≤ u ω)
    (B : Ω → Set ℝ) (hB : ∀ ω, MeasurableSet (B ω)) :
    ∀ ω : Ω,
      (let NX : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict {v : ℝ≥0 |
          0 < v ∧ X.X v ω -
            Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
       NX (Ioc (s ω) (u ω) ×ˢ B ω) =
         NX (Ioc (s ω) (t ω) ×ˢ B ω) +
           NX (Ioc (t ω) (u ω) ×ˢ B ω)) := by
  intro ω
  exact avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive
    X ω (s ω) (t ω) (u ω) (hst ω) (htu ω) (B ω) (hB ω)
