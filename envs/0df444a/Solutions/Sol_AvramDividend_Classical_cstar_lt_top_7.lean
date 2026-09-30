-- Prove2me | solution 7 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T20:56:17.631121+00:00
-- url     : https://prove2.me/submissions/32ed6220-c1c7-4304-9233-408185cba77a
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
  · simpa [cstar, hne] using hfinite hne
  · by_cases hne : (cstarSet W).Nonempty
    · simpa [cstar, hne] using hfinite hne
    · rw [cstar, if_neg hne, if_pos hzero]
      exact ENNReal.zero_lt_top
