-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_piecewise_all_capital_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:38:10.185985+00:00
-- url     : https://prove2.me/submissions/21790704-ced4-4145-a54a-45c1f3cbbb70

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- True reflected dividends at every reserve, expressed entirely in terms
of the genuine boundary expectation, without any scale differentiability. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        if x ≤ a then
          ENNReal.ofReal (W x / W a) * barrierSupValue X a q
        else
          ENNReal.ofReal (x - a) + barrierSupValue X a q := by
  intro x hx
  by_cases hxa : x ≤ a
  · simp only [if_pos hxa]
    exact barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx hxa
  · simp only [if_neg hxa]
    have hax : a < x := lt_of_not_ge hxa
    have ha0 : 0 ≤ a := le_of_lt ha
    have hAd : IsAdmissibleLe X a (ENNReal.ofReal a)
        (barrierStrategy X a a) :=
      barrierStrategy_admissibleLe_nonnegative_barrier X a a ha0 ha0
    have hPay := (add_initial_excess_admissible_value X q x a
      ha0 hax (barrierStrategy X a a) hAd).2
    calc
      dividendValue X q x (barrierStrategy X x a) =
          dividendValue X q x
            (fun t ω => if t = 0 then 0 else
              (x - a) + barrierStrategy X a a t ω) := by
          rw [barrierStrategy_eq_add_initial_excess_above_barrier X x a ha0 hax]
      _ = ENNReal.ofReal (x - a) +
          dividendValue X q a (barrierStrategy X a a) := hPay
      _ = ENNReal.ofReal (x - a) + barrierSupValue X a q := by
          rw [barrierValue_self_eq_barrierSupValue X q a]
