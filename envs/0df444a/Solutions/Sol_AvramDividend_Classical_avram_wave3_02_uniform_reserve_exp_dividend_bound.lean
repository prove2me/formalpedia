-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_reserve_exp_dividend_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:50:29.618859+00:00
-- url     : https://prove2.me/submissions/0098fd96-4cdf-4339-9ada-539d1d47263d

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

/-- A uniform quantitative source-Stieltjes dividend decay bound
holds over every bounded interval of nonnegative initial reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ C : ℝ, 0 < φ ∧ 0 < C ∧
      ∀ R a : ℝ, 0 ≤ R → R + 1 ≤ a →
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        dividendValue X q x (barrierStrategy X x a)) ≤
        ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))) *
          ENNReal.ofReal C := by
  obtain ⟨φ, C, hφ, hC, hbound⟩ :=
    avram_wave3_02_positive_reserve_exp_dividend_bound X hX q hq W hW
  refine ⟨φ, C, hφ, hC, ?_⟩
  intro R a hR hRa
  have hRp : 0 < R + 1 := by linarith
  have ha : 0 ≤ a := by linarith
  refine iSup_le fun x => ?_
  refine iSup_le fun hx => ?_
  have hmono : dividendValue X q x (barrierStrategy X x a) ≤
      dividendValue X q (R + 1) (barrierStrategy X (R + 1) a) :=
    (avram_wave3_02_value_monotone_in_initial_capital X hX q hq W hW a ha)
      (Set.mem_Ici.mpr hx.1) (Set.mem_Ici.mpr (le_of_lt hRp))
      (by linarith [hx.2])
  exact hmono.trans (hbound (R + 1) a hRp hRa)
