-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_original_unit_time_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:57:30.637894+00:00
-- url     : https://prove2.me/submissions/02678b0f-d710-4937-8f72-45bee0f340f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original expected jump counts during the first unit of time
form a genuine measure on real jump marks, without identifying it with ν. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_past_expected_time_mark_occupation_measure
      X 0 Set.univ MeasurableSet.univ
  let S : Set (ℝ≥0 × ℝ) := Ioc 0 (1 : ℝ≥0) ×ˢ Set.univ
  refine ⟨(Q.restrict S).map Prod.snd, ?_⟩
  intro B hB
  have hPre : MeasurableSet ((Prod.snd : ℝ≥0 × ℝ → ℝ) ⁻¹' B) := measurable_snd hB
  have hRect :
      (Prod.snd ⁻¹' B) ∩ S = Ioc 0 (1 : ℝ≥0) ×ˢ B := by
    ext p
    rcases p with ⟨t, y⟩
    simp [S, Set.mem_prod, and_comm, and_left_comm, and_assoc]
  calc
    ((Q.restrict S).map Prod.snd) B =
        Q ((Prod.snd ⁻¹' B) ∩ S) := by
          rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply hPre]
    _ = Q (Ioc 0 (1 : ℝ≥0) ×ˢ B) := by rw [hRect]
    _ = (∫⁻ ω in Set.univ,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) :=
        hQ _ (measurableSet_Ioc.prod hB)
    _ = (∫⁻ ω,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by simp
