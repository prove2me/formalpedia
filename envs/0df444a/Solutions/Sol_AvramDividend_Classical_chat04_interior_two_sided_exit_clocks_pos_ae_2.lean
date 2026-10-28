-- Prove2me | solution 2 for AvramDividend.Classical.chat04_interior_two_sided_exit_clocks_pos_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:43:02.364044+00:00
-- url     : https://prove2.me/submissions/15494503-ae92-4483-b373-77c5f457f6ff

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
import Theorems.Thm_AvramDividend_Classical_chat04_up_exit_time_pos_of_initial_safe_ceiling
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_pos_of_initial_safe_window
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-! Every interior safe window delays both strict passage clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (hx0 : 0 < x) (hxa : x < a) :
    ∀ᵐ ω ∂P,
      0 < twoSidedExitUpTime X (a - x) ω ∧
      0 < twoSidedExitDownTime X (-x) ω := by
  apply Filter.Eventually.of_forall
  intro ω
  obtain ⟨ε, hε, hsafe⟩ :=
    chat04_interior_two_sided_initial_safe_window X a x hx0 hxa ω
  exact ⟨
    chat04_up_exit_time_pos_of_initial_safe_ceiling X (a - x) ω ε hε
      (fun t ht => (hsafe t ht).2),
    chat04_down_exit_time_pos_of_initial_safe_window X x ω ε hε
      (fun t ht => (hsafe t ht).1)⟩
