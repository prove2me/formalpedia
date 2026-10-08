-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_singleton_rightJump_extended
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:03:30.727977+00:00
-- url     : https://prove2.me/submissions/631fc709-5b6f-46fd-b731-3b12fbbb69f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_extension_leftContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_right_jump_of_leftContinuousExtension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ) :
    dividendMeasure D ω {t} =
      ENNReal.ofReal
        (Function.rightLim (fun s : ℝ => D s.toNNReal ω) t -
          D t.toNNReal ω) := by
  exact dividendMeasure_singleton_right_jump_of_leftContinuousExtension
    D hD ω (dividendStrategy_real_extension_leftContinuous D hD ω) t
