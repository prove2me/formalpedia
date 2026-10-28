-- Prove2me | solution 4 for AvramDividend.Classical.vcstar_hjb_all_positive_of_generator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T03:34:56.142003+00:00
-- url     : https://prove2.me/submissions/9535115c-16dd-4b61-815a-5ccda2f84358
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_eq_zero_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith

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
  by_cases hc0 : cstar W = 0
  · exact (vcstar_hjb_all_positive_of_generator_zero_barrier X q W hc0 hgen) y hy
  · have hcpos : (0 : ℝ≥0∞) < cstar W :=
      lt_of_le_of_ne zero_le (Ne.symm hc0)
    rcases lt_trichotomy y (cstar W).toReal with hbelow | heq | habove
    · have hbelowE : ENNReal.ofReal y < cstar W := by
        rw [← ENNReal.ofReal_toReal hc.ne]
        rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt hy)]
        exact hbelow
      exact (vcstar_hjb_below_cstar X hX q hq W hW hc hcpos h_smooth)
        y hy hbelowE
    · subst y
      obtain ⟨hInt, hZero⟩ :=
        vcstar_generator_eq_zero_at_positive_cstar
          X hX q hq W hW hc hcpos h_smooth hgen
      have hDeriv :=
        vcstar_deriv_eq_one_at_positive_cstar
          X hX q hq W hW hc hcpos h_smooth
      refine ⟨hInt, ?_⟩
      rw [hZero, hDeriv]
      norm_num
    · exact (vcstar_hjb_above_cstar_of_generator X q W hgen) y habove
