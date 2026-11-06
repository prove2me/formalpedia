-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_allvariation_root_from_inside_cap_and_top_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:19:25.199986+00:00
-- url     : https://prove2.me/submissions/a4fcb863-d460-4293-9381-1b78ca8f436f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_capped_value_all_capital_without_smoothness
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

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
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    obtain ⟨hD, hValue⟩ :=
      barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
    have hLower :=
      (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
        X hX q hq W hW hc x hx).1
    exact ⟨hD, hValue, le_antisymm (hCapUpper x hx) hLower⟩
  · intro hgen x hx
    obtain ⟨hD, _⟩ :=
      barrier_cstar_attains_value_all_capital X hX q hq W hW hc x hx
    have hLower :=
      (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
        X hX q hq W hW hc x hx).2
    exact ⟨hD.1, le_antisymm (hTopUpper hgen x hx) hLower⟩
