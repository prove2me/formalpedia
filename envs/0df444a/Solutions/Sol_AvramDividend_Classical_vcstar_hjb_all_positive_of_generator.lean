-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:41:58.112417+00:00
-- url     : https://prove2.me/submissions/a34e04ec-4092-4a32-9381-99ee5e588698
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
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
  intro y hy
  let c : ℝ := (cstar W).toReal
  rcases lt_trichotomy y c with hlt | heq | hgt
  · have hcR : 0 < c := lt_trans hy hlt
    have hcpos : 0 < cstar W := (ENNReal.toReal_pos_iff.mp hcR).1
    have hyc : ENNReal.ofReal y < cstar W :=
      (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) (ne_of_lt hc)).mpr
        (by simpa [c] using hlt)
    exact vcstar_hjb_below_cstar X hX q hq W hW hc hcpos h_smooth
      y hy hyc
  · have hcR : 0 < c := by simpa [heq] using hy
    have hcpos : 0 < cstar W := (ENNReal.toReal_pos_iff.mp hcR).1
    rw [heq]
    exact vcstar_hjb_at_positive_cstar X hX q hq W hW
      hc h_smooth hcpos hgen
  · exact vcstar_hjb_above_cstar_of_generator X q W hgen y
      (by simpa [c] using hgt)
