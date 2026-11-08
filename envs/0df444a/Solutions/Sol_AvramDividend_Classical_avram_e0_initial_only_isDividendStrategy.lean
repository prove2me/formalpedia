-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_only_isDividendStrategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:10:34.795099+00:00
-- url     : https://prove2.me/submissions/c9497db1-a03e-4947-80ba-6b9686558a90

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_monotone
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_adapted
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_leftcont
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Assemble the original initial-only dividend strategy from verified fields. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKmeas : Measurable[𝓕 0] K) :
    IsDividendStrategy 𝓕 (fun t ω => if t = 0 then 0 else K ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    simp
  · intro ω
    exact avram_e0_initial_only_dividend_monotone K hKnonneg ω
  · intro ω t
    exact avram_e0_initial_only_dividend_leftcont K ω t
  · exact avram_e0_initial_only_dividend_adapted 𝓕 K hKmeas
