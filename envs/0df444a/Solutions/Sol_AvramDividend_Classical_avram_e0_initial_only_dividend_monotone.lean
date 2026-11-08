-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_dividend_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:49:19.988557+00:00
-- url     : https://prove2.me/submissions/b26488b5-28c0-4d91-bd05-367cc97558cd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Pathwise monotonicity of the single initial-right-payment strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (K : Ω → ℝ) (hK : ∀ ω, 0 ≤ K ω) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => if t = 0 then 0 else K ω) := by
  intro s t hst
  by_cases hs : s = 0
  · subst s
    by_cases ht : t = 0
    · simp [ht]
    · simpa [ht] using hK ω
  · have ht : t ≠ 0 := by
      intro hzero
      subst t
      have hszero : s = 0 := le_antisymm hst (by positivity)
      exact hs hszero
    simp [hs, ht]
