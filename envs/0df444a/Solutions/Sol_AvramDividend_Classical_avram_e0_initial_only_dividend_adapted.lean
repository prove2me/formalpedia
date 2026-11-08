-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_dividend_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:51:12.743238+00:00
-- url     : https://prove2.me/submissions/15e28391-149c-4bc6-ad6a-4d987f71f570

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

/-! Initial-mark measurability makes the single-right-jump dividend adapted. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (K : Ω → ℝ) (hK : Measurable[𝓕 0] K) :
    Adapted 𝓕 (fun t ω => if t = 0 then 0 else K ω) := by
  intro t
  by_cases ht : t = 0
  · subst t
    simpa using (measurable_const : Measurable[𝓕 0] (fun _ : Ω => (0 : ℝ)))
  · have hKt : Measurable[𝓕 t] K :=
      hK.mono (𝓕.mono (by positivity : (0 : ℝ≥0) ≤ t)) le_rfl
    simpa [ht] using hKt
