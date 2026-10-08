-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_before_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:06:02.704995+00:00
-- url     : https://prove2.me/submissions/bc073a51-639e-4b47-9dc7-1b64cae3b7b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (t : ℝ≥0) (ω : Ω)
    (hbelow : ∀ s : ℝ≥0, s ≤ t → X.X s ω ≤ a - x) :
    barrierStrategy X x a t ω = 0 := by
  classical
  by_cases ht : t = 0
  · simp [barrierStrategy, ht]
  · have hsup :
        (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) ≤ a - x := by
      have ht0 : (0 : ℝ≥0) ≤ t := bot_le
      haveI : Nonempty (Icc (0 : ℝ≥0) t) :=
        ⟨⟨0, ⟨le_rfl, ht0⟩⟩⟩
      exact ciSup_le fun s => hbelow s.1 s.2.2
    have hzero :
        x - a + (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) ≤ 0 := by
      linarith
    simp [barrierStrategy, ht, max_eq_left hzero]
