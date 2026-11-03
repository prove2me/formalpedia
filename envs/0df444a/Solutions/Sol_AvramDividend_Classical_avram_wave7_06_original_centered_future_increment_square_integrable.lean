-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_centered_future_increment_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:38:05.044373+00:00
-- url     : https://prove2.me/submissions/790894d9-5df6-4b1c-8f72-32b9ec48f68b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L2_integrable_and_equal_second_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual source mean-centred future increment has an integrable square. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hFirst : Integrable (X.X t) P)
    (hSecond : Integrable (fun ω => (X.X t ω)^2) P) :
    Integrable (fun ω =>
      (X.X (s + t) ω - X.X s ω -
        (∫ η, X.X t η ∂P))^2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let m : ℝ := ∫ η, X.X t η ∂P
  have hShiftFirst : Integrable
      (fun ω => X.X (s + t) ω - X.X s ω) P :=
    (avram_wave7_06_original_future_increment_L1_integrable_equal_mean
      X s t hFirst).1
  have hShiftSecond : Integrable
      (fun ω => (X.X (s + t) ω - X.X s ω)^2) P :=
    (avram_wave7_06_original_future_increment_L2_integrable_and_equal_second_moment
      X s t hSecond).1
  have hLinear : Integrable
      (fun ω => (2 * m) * (X.X (s + t) ω - X.X s ω)) P :=
    hShiftFirst.const_mul (2 * m)
  have hConstant : Integrable (fun _ : Ω => m^2) P :=
    integrable_const _
  have hExpanded : Integrable
      (fun ω => (X.X (s + t) ω - X.X s ω)^2 -
        (2 * m) * (X.X (s + t) ω - X.X s ω) + m^2) P :=
    (hShiftSecond.sub hLinear).add hConstant
  change Integrable
    (fun ω => (X.X (s + t) ω - X.X s ω - m)^2) P
  have hExpansion :
      (fun ω => (X.X (s + t) ω - X.X s ω - m)^2) =
      (fun ω => (X.X (s + t) ω - X.X s ω)^2 -
        (2 * m) * (X.X (s + t) ω - X.X s ω) + m^2) := by
    funext ω
    ring
  rw [hExpansion]
  exact hExpanded
