-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_upperfirst_lintegral_ne_top_finite_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:35:38.985969+00:00
-- url     : https://prove2.me/submissions/984bc127-5f4e-407a-a587-5468a28c902f

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.BoundedOrder.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_lintegral_le_measure_univ

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Killed strict-exit discounted mass is finite under every finite path-space measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    [IsFiniteMeasure μ] (q a x : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≠ ⊤ := by
  have hmass : μ Set.univ ≠ (⊤ : ℝ≥0∞) :=
    measure_ne_top μ Set.univ
  exact ne_top_of_le_ne_top hmass
    (chat04_discounted_upperfirst_lintegral_le_measure_univ X μ q a x hq)
