-- Prove2me | solution 5 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T05:54:11.809548+00:00
-- url     : https://prove2.me/submissions/6a0fb9f9-d376-40a9-a3cb-14dd0d02f8ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar

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
  have hAbove := vcstar_hjb_above_cstar_of_generator X q W hgen
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ cstar W) with hc0 | hcpos
  · intro y hy
    have hc0' : cstar W = 0 := hc0.symm
    have hy_gt : (cstar W).toReal < y := by
      rw [hc0']
      simpa using hy
    exact hAbove y hy_gt
  · have hcpos' : (0 : ℝ≥0∞) < cstar W := hcpos
    have hBelow :=
      vcstar_hjb_below_cstar X hX q hq W hW hc hcpos' h_smooth
    have hAt :=
      vcstar_hjb_at_positive_cstar X hX q hq W hW hc h_smooth hcpos' hgen
    intro y hy
    rcases lt_trichotomy (ENNReal.ofReal y) (cstar W) with hlt | heq | hgt
    · exact hBelow y hy hlt
    · have hy_eq : y = (cstar W).toReal := by
        have h1 : (ENNReal.ofReal y).toReal = (cstar W).toReal := by
          rw [heq]
        have h2 : (ENNReal.ofReal y).toReal = y :=
          ENNReal.toReal_ofReal (le_of_lt hy)
        rw [h2] at h1
        exact h1
      rw [hy_eq]
      exact hAt
    · have h_toReal_lt : (cstar W).toReal < (ENNReal.ofReal y).toReal :=
        (ENNReal.toReal_lt_toReal (ne_of_lt hc) (by simp)).mpr hgt
      have hy_gt : (cstar W).toReal < y := by
        rwa [ENNReal.toReal_ofReal (le_of_lt hy)] at h_toReal_lt
      exact hAbove y hy_gt
