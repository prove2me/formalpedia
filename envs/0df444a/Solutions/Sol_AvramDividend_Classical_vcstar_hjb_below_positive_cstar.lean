-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_below_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:26:53.0147+00:00
-- url     : https://prove2.me/submissions/94c05e11-659e-4be7-a636-98a9749c0c76
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcfin : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W) :
    ∀ y : ℝ, 0 < y → ENNReal.ofReal y < cstar W →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
          (1 - deriv (vcstar W) y) = 0 := by
  have hreg : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal) := by
    rcases h_smooth with hσ | hBV | hC2
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hBV)
    · exact Or.inr (Or.inr (hC2.mono (by
        intro z hz
        exact hz.1)))
  have hgen :=
    generator_vcstar_eq_zero X hX q hq W hW hreg hcpos
  have hder := vcstar_deriv_ge_one X hX q hq W hW
  intro y hy hycap
  have hybar : y < (cstar W).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal
      (le_of_lt hy) (ne_of_lt hcfin)).mp hycap
  obtain ⟨hdom, heq⟩ := hgen y ⟨hy, hybar⟩
  have hle : 1 - deriv (vcstar W) y ≤ 0 :=
    sub_nonpos.mpr (hder y hy).2
  refine ⟨hdom, ?_⟩
  rw [heq]
  exact max_eq_left hle
