-- Prove2me | solution 6 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:46:55.321466+00:00
-- url     : https://prove2.me/submissions/2b04ea56-fb12-4e1f-97e0-8cf40cdf15c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator

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
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  rcases lt_trichotomy (ENNReal.ofReal y) (cstar W) with hlt | heq | hgt
  · have hcpos : 0 < cstar W := lt_of_le_of_lt zero_le hlt
    exact vcstar_hjb_below_cstar X hX q hq W hW hc hcpos h_smooth y hy hlt
  · have hcpos : 0 < cstar W := by
      rw [← heq]
      exact ENNReal.ofReal_pos.mpr hy
    have hy_eq : y = (cstar W).toReal := by
      have hto : (ENNReal.ofReal y).toReal = (cstar W).toReal := by rw [heq]
      rwa [ENNReal.toReal_ofReal (le_of_lt hy)] at hto
    have hat :=
      vcstar_hjb_at_positive_cstar X hX q hq W hW hc h_smooth hcpos hgen
    rw [hy_eq]
    exact hat
  · have hlt : (cstar W).toReal < y := by
      have hne1 : cstar W ≠ ⊤ := hc.ne
      have hne2 : ENNReal.ofReal y ≠ ⊤ := ENNReal.ofReal_ne_top
      have h1 : (cstar W).toReal < (ENNReal.ofReal y).toReal :=
        (ENNReal.toReal_lt_toReal hne1 hne2).mpr hgt
      rwa [ENNReal.toReal_ofReal (le_of_lt hy)] at h1
    exact vcstar_hjb_above_cstar_of_generator X q W hgen y hlt
