-- Prove2me | solution 1 for AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:56:19.651267+00:00
-- url     : https://prove2.me/submissions/8d07dc34-e176-41b2-b5ba-c5d8a0d4b466

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_countable_grid
import Theorems.Thm_AvramDividend_Classical_countableSchedule_upper_grid_clock_eq_subtype_inf
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Compose the pathwise strict upper clock with its measurable enumeration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (upper : ℝ) :
    (⨅ i : {t : ℝ≥0 // upper < X.X t ω}, (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if upper <
          X.X (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) ω
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) := by
  classical
  trans (⨅ i : {p : ℕ × ℕ // 0 < p.1 ∧
      upper < X.X ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) ω},
      (((i.1.2 : ℝ≥0) * (i.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞))
  · exact levy_strictUpper_exit_subtype_inf_eq_countable_grid X ω upper
  · exact (countableSchedule_upper_grid_clock_eq_subtype_inf
      (fun t : ℝ≥0 => X.X t ω) upper).symm
