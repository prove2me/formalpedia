-- Prove2me | solution 7 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:54:29.161496+00:00
-- url     : https://prove2.me/submissions/55125daf-60a6-4ada-8717-38ae827e2126
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Repair of CE 17478 (E01): `lt_of_le_of_ne'` at this revision expects `b ≠ a`
-- (cstar W ≠ 0), but the submitted hypothesis was `0 ≠ cstar W`. The causal fix
-- is `Ne.symm`; no other logic changes.
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
  by_cases hc0 : cstar W = 0
  · intro y hy0
    exact AvramDividend.Classical.vcstar_hjb_all_positive_of_generator_zero_barrier
      X q W hc0 hgen y hy0
  · have h0ne : (0 : ENNReal) ≠ cstar W := Ne.symm hc0
    have h0le : (0 : ENNReal) ≤ cstar W := zero_le
    have hcpos : (0 : ENNReal) < cstar W := lt_of_le_of_ne' h0le (Ne.symm h0ne)
    have hcne : cstar W ≠ ⊤ := ne_of_lt hc
    intro y hy0
    rcases lt_trichotomy y (cstar W).toReal with hlt | heq | hgt
    · have hlt_enn : ENNReal.ofReal y < cstar W := by
        have h := (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hcne).mpr hlt
        exact h
      exact AvramDividend.Classical.vcstar_hjb_below_cstar
        X hX q hq W hW hc hcpos h_smooth y hy0 hlt_enn
    · subst heq
      exact AvramDividend.Classical.vcstar_hjb_at_positive_cstar
        X hX q hq W hW hc h_smooth hcpos hgen
    · exact AvramDividend.Classical.vcstar_hjb_above_cstar_of_generator
        X q W hgen y hgt
