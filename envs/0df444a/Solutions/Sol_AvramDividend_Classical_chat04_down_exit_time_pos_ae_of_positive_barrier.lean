-- Prove2me | solution 1 for AvramDividend.Classical.chat04_down_exit_time_pos_ae_of_positive_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:20:04.791405+00:00
-- url     : https://prove2.me/submissions/a8847d30-8412-4c91-a282-42bbe4250619

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_initial_safe_window_of_rightCont_zero
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-! A positive downward barrier distance gives an a.s. positive down-crossing time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a : ℝ) (ha : 0 < a) :
    ∀ᵐ ω ∂P, 0 < twoSidedExitDownTime X (-a) ω := by
  apply Filter.Eventually.of_forall
  intro ω
  obtain ⟨ε, hε, hsafe⟩ :=
    chat04_initial_safe_window_of_rightCont_zero X a ha ω (X.X_zero ω)
  exact chat04_down_exit_time_pos_of_initial_safe_window X a ω ε hε hsafe
