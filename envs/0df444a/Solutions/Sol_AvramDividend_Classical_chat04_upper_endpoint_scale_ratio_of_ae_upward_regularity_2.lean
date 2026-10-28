-- Prove2me | solution 2 for AvramDividend.Classical.chat04_upper_endpoint_scale_ratio_of_ae_upward_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:03:40.023003+00:00
-- url     : https://prove2.me/submissions/5676f51f-bde6-4f3a-af2f-f30f37b00686

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Exact x=a scale ratio with almost-sure upward regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a =
      ENNReal.ofReal (W a / W a) := by
  rw [chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
      X q a ha hplus,
    div_self (scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha).ne',
    ENNReal.ofReal_one]
