-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_above_value_eq_initial_excess_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:51:47.719927+00:00
-- url     : https://prove2.me/submissions/55a2178a-cc9c-406c-bea4-898c4b15b905

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Above a nonnegative barrier, the original dividend process first pays
the excess and then starts the reflected process from the barrier. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ)
    (ha : 0 ≤ a) (hax : a < x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (x - a) + barrierSupValue X a q := by
  have hAd : IsAdmissibleLe X a (ENNReal.ofReal a)
      (barrierStrategy X a a) :=
    barrierStrategy_admissibleLe_nonnegative_barrier X a a ha ha
  have hPay := (add_initial_excess_admissible_value X q x a
    ha hax (barrierStrategy X a a) hAd).2
  calc
    dividendValue X q x (barrierStrategy X x a) =
        dividendValue X q x
          (fun t ω => if t = 0 then 0 else
            (x - a) + barrierStrategy X a a t ω) := by
        rw [barrierStrategy_eq_add_initial_excess_above_barrier X x a ha hax]
    _ = ENNReal.ofReal (x - a) +
        dividendValue X q a (barrierStrategy X a a) := hPay
    _ = ENNReal.ofReal (x - a) + barrierSupValue X a q := by
        rw [barrierValue_self_eq_barrierSupValue X q a]
