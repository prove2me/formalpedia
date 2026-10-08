-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_below_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:05:29.75417+00:00
-- url     : https://prove2.me/submissions/15c4427c-54f4-49db-8a15-ea134a0ffd93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  have hctop : cstar W ≠ ⊤ := ne_of_lt hc
  have hgenSmooth :
      0 < X.σ ∨ X.BoundedVariation ∨
        ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with hσ | hrest
    · exact Or.inl hσ
    · rcases hrest with hbv | htwo
      · exact Or.inr (Or.inl hbv)
      · exact Or.inr (Or.inr (htwo.mono (by
          intro z hz
          exact hz.1)))
  intro y hy hyc
  have hycR : y < (cstar W).toReal := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy.le hctop).mp hyc
  have hgen :=
    generator_vcstar_eq_zero X hX q hq W hW hgenSmooth hcpos y
      ⟨hy, hycR⟩
  have hder := vcstar_deriv_ge_one X hX q hq W hW y hy
  refine ⟨hgen.1, ?_⟩
  have hmarg : 1 - deriv (vcstar W) y ≤ 0 := by
    linarith [hder.2]
  simp [hgen.2, hmarg]
