-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_two_separated_marked_increment_cells_probability_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:36:13.132686+00:00
-- url     : https://prove2.me/submissions/f86ecc6a-5527-45f0-aec3-d4b798a61887

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_past_event_next_levy_increment_measure_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s a b c d : ℝ≥0) (hsa : s ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P (A ∩ ({ω | X.X b ω - X.X a ω ∈ B} ∩
      {ω | X.X d ω - X.X c ω ∈ C})) =
    P A * P {ω | X.X b ω - X.X a ω ∈ B} *
      P {ω | X.X d ω - X.X c ω ∈ C} := by
  let E : Set Ω := {ω | X.X b ω - X.X a ω ∈ B}
  have hb : Measurable[𝓕 c] (X.X b) :=
    (X.adapted b).mono (𝓕.mono hbc) le_rfl
  have ha : Measurable[𝓕 c] (X.X a) :=
    (X.adapted a).mono (𝓕.mono (hab.trans hbc)) le_rfl
  have hE : MeasurableSet[𝓕 c] E := hB.preimage (hb.sub ha)
  have hAc : MeasurableSet[𝓕 c] A :=
    (𝓕.mono (hsa.trans (hab.trans hbc))) A hA
  have hPast : MeasurableSet[𝓕 c] (A ∩ E) := hAc.inter hE
  have hAa : MeasurableSet[𝓕 a] A := (𝓕.mono hsa) A hA
  have hFirst :=
    chat04_past_event_next_levy_increment_measure_product
      X a b hab A hAa B hB
  have hSecond :=
    chat04_past_event_next_levy_increment_measure_product
      X c d hcd (A ∩ E) hPast C hC
  change P (A ∩ (E ∩ {ω | X.X d ω - X.X c ω ∈ C})) =
    P A * P E * P {ω | X.X d ω - X.X c ω ∈ C}
  calc
    P (A ∩ (E ∩ {ω | X.X d ω - X.X c ω ∈ C})) =
        P ((A ∩ E) ∩ {ω | X.X d ω - X.X c ω ∈ C}) := by
          rw [Set.inter_assoc]
    _ = P (A ∩ E) * P {ω | X.X d ω - X.X c ω ∈ C} := hSecond
    _ = (P A * P E) * P {ω | X.X d ω - X.X c ω ∈ C} := by
          rw [hFirst]
    _ = P A * P E * P {ω | X.X d ω - X.X c ω ∈ C} := rfl
