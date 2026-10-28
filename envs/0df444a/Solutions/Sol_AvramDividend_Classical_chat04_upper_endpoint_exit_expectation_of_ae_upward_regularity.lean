-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:56:47.980637+00:00
-- url     : https://prove2.me/submissions/a38f3d23-2cdb-4b74-8a92-2502616991cf

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-! Remove the downward safe-window assumption using actual path regularity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a : ℝ) (ha : 0 < a)
    (hplus : ∀ᵐ ω ∂P,
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    twoSidedExitExpectation X q a a = 1 := by
  apply chat04_upper_endpoint_exit_expectation_of_ae_regular_windows
    X q a hplus
  exact Filter.Eventually.of_forall (fun ω =>
    chat04_initial_safe_window_of_rightCont_zero
      X a ha ω (X.X_zero ω))
