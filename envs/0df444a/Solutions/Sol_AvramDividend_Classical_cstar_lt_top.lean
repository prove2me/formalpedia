-- Prove2me | solution 1 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T00:59:24.059789+00:00
-- url     : https://prove2.me/submissions/74fa3b74-2f3e-4a17-b8f1-a467bde0a008
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained

open MeasureTheory Filter Set
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Lemma 2(i): the barrier level c* is finite.
--
-- `cstar` is defined by three branches and only the third yields the top value:
-- if `cstarSet W` is nonempty, `cstar W` is the infimum of `ENNReal.ofReal a`
-- over that set; else if `W'(0+) <= W'(x)` for every `x > 0`, `cstar W = 0`;
-- else `cstar W` is the top value. The first two branches are strictly below
-- the top value, and the third is ruled out by `scaleDeriv_inf_attained`.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  have hmin :
      (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
        ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) :=
    scaleDeriv_inf_attained X hX q hq W hW
  have hne_or : (cstarSet W).Nonempty ∨
      (∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal)) := by
    rcases hmin with ⟨a, ha, hag⟩ | hd
    · exact Or.inl ⟨a, ha, hag⟩
    · exact Or.inr hd
  rcases hne_or with ⟨a₀, ha₀⟩ | hdz
  · -- First branch: the infimum is bounded above by one of its members.
    have hne1 : (cstarSet W).Nonempty := ⟨a₀, ha₀⟩
    have hle : (⨅ a ∈ cstarSet W, ENNReal.ofReal a) ≤ ENNReal.ofReal a₀ :=
      biInf_le (ENNReal.ofReal : ℝ → ℝ≥0∞) ha₀
    rw [cstar, if_pos hne1]
    exact hle.trans_lt ENNReal.ofReal_lt_top
  · -- Second branch: `cstar W = 0`.
    by_cases hne2 : (cstarSet W).Nonempty
    · rw [cstar, if_pos hne2]
      obtain ⟨b, hb⟩ : ∃ a : ℝ, a ∈ cstarSet W := hne2
      exact (biInf_le (ENNReal.ofReal : ℝ → ℝ≥0∞) hb).trans_lt
        ENNReal.ofReal_lt_top
    · rw [cstar, if_neg hne2, if_pos hdz]
      exact ENNReal.zero_lt_top
