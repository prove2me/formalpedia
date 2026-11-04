-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_past_campbell_eq_negative_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:56:24.326227+00:00
-- url     : https://prove2.me/submissions/ef2f78a3-0b22-4d6d-8f85-4dca8fe81ad8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- For every original past event, the Campbell mean measure of original
intrinsic jumps is exactly its negative-mark measure restriction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ (C : Set (ℝ≥0 × ℝ)), MeasurableSet C →
        Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P)) ∧
      Q = Q.restrict (Set.univ ×ˢ Iio (0 : ℝ)) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_past_expected_time_mark_occupation_measure X s A hA
  refine ⟨Q, hQ, ?_⟩
  apply Measure.ext
  intro C hC
  have hNeg : MeasurableSet ((Set.univ : Set ℝ≥0) ×ˢ Iio (0 : ℝ)) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Iio
  have hInter : MeasurableSet (C ∩ (Set.univ ×ˢ Iio (0 : ℝ))) :=
    hC.inter hNeg
  calc
    Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) :=
      hQ C hC
    _ = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (C ∩ (Set.univ ×ˢ Iio (0 : ℝ))) ∂P) := by
      apply lintegral_congr
      intro ω
      exact avram_p2_d_future_full_time_mark_negative_support X ω C hC
    _ = Q (C ∩ (Set.univ ×ˢ Iio (0 : ℝ))) := (hQ _ hInter).symm
    _ = (Q.restrict (Set.univ ×ˢ Iio (0 : ℝ))) C :=
      (Measure.restrict_apply hC).symm
