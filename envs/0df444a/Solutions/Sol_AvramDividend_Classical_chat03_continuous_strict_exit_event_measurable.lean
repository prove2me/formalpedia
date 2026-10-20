-- Prove2me | solution 1 for AvramDividend.Classical.chat03_continuous_strict_exit_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:16:30.482211+00:00
-- url     : https://prove2.me/submissions/c6775eb7-8e7f-421e-b0c3-af098641c29a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff
import Theorems.Thm_AvramDividend_Classical_chat03_countable_grid_exit_event_measurable
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
Continuous strict-exit occurrence is measurable because a strict exit
is equivalent to a countable inverse-natural grid strict exit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω | ∃ t : ℝ≥0,
        X.X t ω < lower ∨ upper < X.X t ω} := by
  have hGrid :=
    chat03_countable_grid_exit_event_measurable X lower upper
  have hEq :
      {ω : Ω | ∃ t : ℝ≥0,
        X.X t ω < lower ∨ upper < X.X t ω} =
      {ω : Ω | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    ext ω
    exact chat03_countable_inverse_nat_grid_exit_iff X ω lower upper
  rw [hEq]
  exact hGrid
