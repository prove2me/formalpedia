-- Prove2me | solution 1 for AvramDividend.Classical.chat01_history_killed_lintegral_le_terminal_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:44:14.665236+00:00
-- url     : https://prove2.me/submissions/90461d06-ffae-4c17-b5dc-50cc73d300f6

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Whole-history survival gives no more discounted scale mass than
    terminal-only nonnegativity, even when a path re-enters after ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) ≤
    (∫⁻ ω, ({ω | 0 ≤ x + X.X t ω}).indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) := by
  apply lintegral_mono
  intro ω
  by_cases hsurv : ω ∈ {ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}
  · have hterminal : ω ∈ {ω | 0 ≤ x + X.X t ω} := hsurv t le_rfl
    simp only [Set.indicator_of_mem hsurv, Set.indicator_of_mem hterminal]
    exact le_rfl
  · rw [Set.indicator_of_notMem hsurv]
    exact bot_le
