-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_payoff_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:55:36.778983+00:00
-- url     : https://prove2.me/submissions/50422706-38ca-43ba-a4f7-c667d051e998

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    ∀ (t : ℝ≥0) (ω : Ω),
      0 ≤ ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) := by
  intro t ω
  have hWnn : 0 ≤ W (x + X.X t ω) := by
    by_cases hneg : x + X.X t ω < 0
    · rw [hW.1 _ hneg]
    · exact hW.2.1 _ (le_of_not_gt hneg)
  by_cases hsurv : ω ∈ {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  · rw [Set.indicator_of_mem hsurv]
    exact mul_nonneg (Real.exp_pos _).le hWnn
  · rw [Set.indicator_of_notMem hsurv]
