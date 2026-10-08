-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_singleton_eq_rightLimit_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:12:49.844404+00:00
-- url     : https://prove2.me/submissions/7e8a29fc-8324-45db-a38a-f39136895761

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_rightJump_extended
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    dividendMeasure D ω {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω) := by
  have hAtom :=
    dividendMeasure_singleton_rightJump_extended D hD ω (t : ℝ)
  rw [dividendPath_real_rightLim_eq_rightLimit D ω (hD.2.1 ω) t] at hAtom
  simpa only [Real.toNNReal_coe] using hAtom
