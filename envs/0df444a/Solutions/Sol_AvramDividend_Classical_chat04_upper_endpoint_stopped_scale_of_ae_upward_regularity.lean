-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_stopped_scale_of_ae_upward_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:00:09.65208+00:00
-- url     : https://prove2.me/submissions/a006125d-ecec-4a03-b47d-b8ae29dd2587

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The stopped-scale formula at x=a requires only upward regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W a) := by
  rw [chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
    X q a ha hplus]
  simp
