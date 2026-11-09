-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_single_step_dividend_strategy_of_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:36:20.01038+00:00
-- url     : https://prove2.me/submissions/91205dbb-6210-4234-955f-337aa40e141a

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail13_single_step_left_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original single-clock dividend step is a strategy when adapted and its
payment amount is nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (K : Ω → ℝ)
    (hK : ∀ ω, 0 ≤ K ω)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω)
    (hAdapt : Adapted 𝓕 D) :
    IsDividendStrategy 𝓕 D := by
  refine ⟨?_, ?_, ?_, hAdapt⟩
  · intro ω
    rw [hD]
    simp
  · intro ω t u htu
    change D t ω ≤ D u ω
    rw [hD t ω, hD u ω]
    by_cases ht : t ≤ s
    · rw [if_pos ht]
      by_cases hu : u ≤ s
      · rw [if_pos hu]
      · rw [if_neg hu]
        exact hK ω
    · have hu : ¬u ≤ s := fun hus => ht (le_trans htu hus)
      rw [if_neg ht, if_neg hu]
  · exact avram_bv_tail13_single_step_left_continuity D s K hD
