-- Prove2me | solution 5 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T20:25:16.052208+00:00
-- url     : https://prove2.me/submissions/b916a40e-5cb3-47df-bf1b-ffae0d0ab633
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  have hdich :
      (cstarSet W).Nonempty ∨
        ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
    rcases scaleDeriv_inf_attained X hX q hq W hW with h | h
    · rcases h with ⟨a, ha, hmin⟩
      exact Or.inl ⟨a, ha, hmin⟩
    · exact Or.inr h
  have hfinite (hne : (cstarSet W).Nonempty) :
      (⨅ a ∈ cstarSet W, ENNReal.ofReal a) < ⊤ := by
    rcases hne with ⟨a, ha⟩
    exact lt_of_le_of_lt (iInf₂_le a ha) ENNReal.ofReal_lt_top
  rcases hdich with hne | hzero
  · rw [cstar, if_pos hne]
    exact hfinite hne
  · by_cases hne : (cstarSet W).Nonempty
    · rw [cstar, if_pos hne]
      exact hfinite hne
    · rw [cstar, if_neg hne, if_pos hzero]
      exact ENNReal.zero_lt_top
