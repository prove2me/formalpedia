-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_source_fixed_terminal_strict_drawdown_full_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:26:53.898461+00:00
-- url     : https://prove2.me/submissions/0f6f7056-9c7d-47a9-b51b-2938738517ed

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fixed_horizon_strict_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original unbounded-variation Lévy paths do not finish a positive deterministic
horizon at a running maximum, in the strict terminal drawdown sense. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (T : ℝ≥0) (hT : 0 < T) :
    P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < 0} =
      P Set.univ := by
  have hNeg : ∀ᵐ ω ∂P,
      ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < 0 := by
    filter_upwards [ae_negative_near_zero_of_unbounded_variation X hBV] with ω hω
    obtain ⟨s, hs, hneg⟩ := hω T hT
    refine ⟨s, le_of_lt hs, ?_⟩
    simpa [X.X_zero ω] using hneg
  have hMeasure :
      P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < 0} =
        P Set.univ := by
    apply measure_congr
    filter_upwards [hNeg] with ω hω
    apply propext
    exact ⟨fun _ => Set.mem_univ ω, fun _ => hω⟩
  calc
    _ = P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < 0} :=
      avram_ws01e_b_fixed_horizon_strict_reversal X T hT 0
    _ = P Set.univ := hMeasure
