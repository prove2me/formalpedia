-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_positive_reserve_exp_dividend_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:38:19.407044+00:00
-- url     : https://prove2.me/submissions/e396c536-8caf-450b-8246-e1480a97528f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_ratio_exp_bound
import Theorems.Thm_AvramDividend_Classical_barrier_value_scale_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine discounted dividend value decays at an exponential
rate in the barrier gap when reserve x is positive and x ≤ barrier a. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ C : ℝ, 0 < φ ∧ 0 < C ∧
      ∀ x a : ℝ, 0 < x → x ≤ a →
        dividendValue X q x (barrierStrategy X x a) ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))) * ENNReal.ofReal C := by
  obtain ⟨φ, hφ, hratio⟩ :=
    avram_wave3_02_esscher_ratio_exp_bound X hX q hq W hW
  obtain ⟨C, hC, hbound⟩ :=
    avram_wave3_02_standing_uniform_boundary_reward X hX q hq W hW
  refine ⟨φ, C, hφ, hC, ?_⟩
  intro x a hx hxa
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have heq := (barrier_value_scale_factor
    X hX q hq W hW a ha x (le_of_lt hx) hxa).2
  rw [heq, barrierValue_self_eq_barrierSupValue X q a]
  calc
    ENNReal.ofReal (W x / W a) * barrierSupValue X a q ≤
        ENNReal.ofReal (Real.exp (-φ * (a - x))) * barrierSupValue X a q := by
      gcongr
      exact hratio x a hx hxa
    _ ≤ ENNReal.ofReal (Real.exp (-φ * (a - x))) * ENNReal.ofReal C := by
      gcongr
      exact hbound a (le_of_lt ha)
