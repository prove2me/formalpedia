-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_except_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:17:19.859262+00:00
-- url     : https://prove2.me/submissions/5bd9e55d-5643-4bd5-8800-57954756ab7e

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar_bv_20261027
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine BV HJB identity away from the single switching reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y → y ≠ (cstar W).toReal →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  intro y hy hyne
  rcases lt_or_gt_of_ne hyne with hbelow | habove
  · have hcpos : (0 : ENNReal) < cstar W := by
      by_contra hnon
      have hz : cstar W = 0 :=
        le_antisymm (le_of_not_gt hnon) bot_le
      have hneg : y < (0 : ℝ) := by
        simpa [hz] using hbelow
      exact (not_lt_of_ge (le_of_lt hy) hneg).elim
    exact vcstar_hjb_below_positive_cstar_bv_20261027
      X hX q hq W hW hbv hcpos y ⟨hy, hbelow⟩
  · exact vcstar_hjb_above_cstar_of_generator
      X q W hgen y habove
