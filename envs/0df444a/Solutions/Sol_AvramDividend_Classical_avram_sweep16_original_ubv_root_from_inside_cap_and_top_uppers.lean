-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_root_from_inside_cap_and_top_uppers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:15:27.603253+00:00
-- url     : https://prove2.me/submissions/fc1d06b7-6a67-42b2-9f8f-7c8d0c452c65

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_capped_value_all_capital_without_smoothness
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_root_suffices_strict_positive_reserve

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
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hInsideCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ cstar W →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x))
    (hTopUpper :
      (∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y →
          X.GeneratorIntegrable (vcstar W) y ∧
            X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hCapUpper :=
    avram_sweep17_cstar_capped_value_all_capital_without_smoothness
      X hX q hq W hW hc hInsideCap
  have hLower :=
    avram_sweep16_barrier_cstar_lower_bounds_from_attainment
      X hX q hq W hW hc
  have hCapPositive :
      ∀ x : ℝ, 0 < x →
        valueFunctionLe X q (cstar W) x =
          ENNReal.ofReal (vcstar W x) := by
    intro x hx
    exact le_antisymm (hCapUpper x (le_of_lt hx))
      (hLower x (le_of_lt hx)).1
  have hTopPositive :
      (∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 < x →
        valueFunction X q x = ENNReal.ofReal (vcstar W x) := by
    intro hgen x hx
    exact le_antisymm (hTopUpper hgen x (le_of_lt hx))
      (hLower x (le_of_lt hx)).2
  exact
    avram_sweep16_original_ubv_root_suffices_strict_positive_reserve
      X hX hBV q hq W hW hCapPositive hTopPositive
