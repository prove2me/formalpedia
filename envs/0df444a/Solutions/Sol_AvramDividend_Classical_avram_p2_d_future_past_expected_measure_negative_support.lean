-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_past_expected_measure_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:38:25.730894+00:00
-- url     : https://prove2.me/submissions/afb30b04-ffc2-4ec1-a3f0-d89fd6d1e0ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_full_time_mark_negative_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original past-event expected time-mark count measure is concentrated
on strictly negative marks; no identity with the Levy intensity is assumed. -/
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
      (∀ (C : Set (ℝ≥0 × ℝ)), MeasurableSet C →
        C ⊆ (Set.univ ×ˢ Ici (0 : ℝ)) → Q C = 0) := by
  classical
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_past_expected_time_mark_occupation_measure X s A hA
  refine ⟨Q, hQ, ?_⟩
  intro C hC hNonneg
  have hEmpty :
      C ∩ (Set.univ ×ˢ Iio (0 : ℝ)) = (∅ : Set (ℝ≥0 × ℝ)) := by
    ext z
    constructor
    · intro hz
      have hzNonneg : 0 ≤ z.2 := (hNonneg hz.1).2
      have hzNeg : z.2 < 0 := hz.2.2
      exact False.elim (not_lt_of_ge hzNonneg hzNeg)
    · intro hz
      exact False.elim ((Set.mem_empty_iff_false z).mp hz)
  have hZero (ω : Ω) :
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C = 0 := by
    rw [avram_p2_d_future_full_time_mark_negative_support X ω C hC]
    simp only [hEmpty, measure_empty]
  calc
    Q C = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) C ∂P) := hQ C hC
    _ = 0 := by
      simp only [hZero, lintegral_zero]
