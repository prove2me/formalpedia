-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_single_step_adapted_of_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:27:12.087854+00:00
-- url     : https://prove2.me/submissions/c0e3a8fe-7739-4e24-be6b-234d301b9f93

import Mathlib
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A payment amount measurable at the deterministic clock produces an
adapted original dividend step when payment occurs strictly after that clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (s : ℝ≥0)
    (K : Ω → ℝ) (hK : Measurable[𝓕 s] K) :
    Adapted 𝓕 (fun t ω => if t ≤ s then (0 : ℝ) else K ω) := by
  intro t
  by_cases ht : t ≤ s
  · simpa [ht] using
      (measurable_const : Measurable[𝓕 t] (fun _ : Ω => (0 : ℝ)))
  · have hst : s ≤ t := le_of_lt (lt_of_not_ge ht)
    have hKt : Measurable[𝓕 t] K :=
      hK.mono (𝓕.mono hst) le_rfl
    simpa [ht] using hKt
