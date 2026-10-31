-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_all_capital_exp_dividend_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:45:18.774739+00:00
-- url     : https://prove2.me/submissions/8d5cae05-4525-4376-a229-e123865b0236

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_exp_dividend_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A single exponential barrier-gap bound controls the actual Stieltjes
dividend value at every nonnegative starting reserve, including zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ C : ℝ, 0 < φ ∧ 0 < C ∧
      ∀ x a : ℝ, 0 ≤ x → x + 1 ≤ a →
        dividendValue X q x (barrierStrategy X x a) ≤
          ENNReal.ofReal (Real.exp (-φ * (a - (x + 1)))) *
            ENNReal.ofReal C := by
  obtain ⟨φ, C, hφ, hC, hbound⟩ :=
    avram_wave3_02_positive_reserve_exp_dividend_bound X hX q hq W hW
  refine ⟨φ, C, hφ, hC, ?_⟩
  intro x a hx hxa
  have hxp : 0 < x + 1 := by linarith
  have ha : 0 ≤ a := by linarith
  have hmono : dividendValue X q x (barrierStrategy X x a) ≤
      dividendValue X q (x + 1) (barrierStrategy X (x + 1) a) :=
    (avram_wave3_02_value_monotone_in_initial_capital
      X hX q hq W hW a ha)
      (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (le_of_lt hxp))
      (by linarith)
  exact hmono.trans (hbound (x + 1) a hxp hxa)
