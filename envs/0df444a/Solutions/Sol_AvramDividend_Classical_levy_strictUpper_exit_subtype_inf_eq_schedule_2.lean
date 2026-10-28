-- Prove2me | solution 2 for AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_schedule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:57:21.662602+00:00
-- url     : https://prove2.me/submissions/e40b6109-dd44-4d60-b725-02cfa598302a

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_countable_grid
import Theorems.Thm_AvramDividend_Classical_countableSchedule_upper_grid_clock_eq_subtype_inf

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
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
  exact (AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_countable_grid X ω upper).trans
    (AvramDividend.Classical.countableSchedule_upper_grid_clock_eq_subtype_inf (fun t => X.X t ω) upper).symm
