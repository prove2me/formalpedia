-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_singleton_rightLim_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:51:38.242077+00:00
-- url     : https://prove2.me/submissions/9b841336-11fc-4f8a-a2b4-6edc8a5c087a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ) :
    dividendMeasure D ω {t} =
      ENNReal.ofReal
        (Function.rightLim (fun s : ℝ => D s.toNNReal ω) t -
          Function.leftLim (Function.rightLim
            (fun s : ℝ => D s.toNNReal ω)) t) := by
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro a b hab
    exact (hD.2.1 ω) (Real.toNNReal_mono hab)
  unfold dividendMeasure
  rw [dif_pos hmono]
  exact (hmono.stieltjesFunction.measure_singleton t)
