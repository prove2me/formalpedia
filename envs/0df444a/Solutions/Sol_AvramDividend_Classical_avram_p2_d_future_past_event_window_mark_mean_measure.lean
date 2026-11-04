-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_past_event_window_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:05:42.193195+00:00
-- url     : https://prove2.me/submissions/12b84e67-d315-4a28-b6a5-24f3ba1051d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original expected marked counts over a past event form a genuine
mark measure on any deterministic future time window, without a ν-rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      ρ B = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_past_expected_time_mark_occupation_measure
      X s A hA
  let S : Set (ℝ≥0 × ℝ) := Ioc s t ×ˢ Set.univ
  refine ⟨(Q.restrict S).map Prod.snd, ?_⟩
  intro B hB
  have hPre : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) := measurable_snd hB
  have hRect :
      (Prod.snd ⁻¹' B) ∩ S = Ioc s t ×ˢ B := by
    ext p
    rcases p with ⟨u, y⟩
    simp [S, Set.mem_prod, and_comm, and_left_comm, and_assoc]
  calc
    ((Q.restrict S).map Prod.snd) B =
        Q ((Prod.snd ⁻¹' B) ∩ S) := by
          rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply hPre]
    _ = Q (Ioc s t ×ˢ B) := by rw [hRect]
    _ = (∫⁻ ω in A,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P) :=
        hQ _ (measurableSet_Ioc.prod hB)