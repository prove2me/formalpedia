-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_null_past_event_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:13:36.817198+00:00
-- url     : https://prove2.me/submissions/dbf5b246-e02a-415d-bb90-13cf37509327

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A null original past event contributes zero expected marked jumps,
even when the unconditional original expected count is infinite. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNull : P A = 0) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) = 0 := by
  rw [avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate
    X s t hst A hA B hB, hNull]
  simp
