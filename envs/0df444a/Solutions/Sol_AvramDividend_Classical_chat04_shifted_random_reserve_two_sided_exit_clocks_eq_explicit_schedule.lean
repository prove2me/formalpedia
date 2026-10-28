-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:06:24.244223+00:00
-- url     : https://prove2.me/submissions/b9ecc219-7dd7-4cad-beb2-21c9d864f5bf

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
import Theorems.Thm_AvramDividend_Classical_levy_shiftedLower_strictCrossing_rightInterval
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Both strict exit clocks of a shifted Lévy reserve have explicit countable forms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b : ℝ≥0) :
    (let g : ℝ≥0 → ℝ := fun t => X.X (b + t) ω - X.X b ω
     let τ : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     (⨅ i : {t : ℝ≥0 // a - H ω < g t}, (i.1 : ℝ≥0∞)) =
       (⨅ j : ℕ, if a - H ω < g (τ j) then (τ j : ℝ≥0∞) else ⊤) ∧
     (⨅ i : {t : ℝ≥0 // g t < -H ω}, (i.1 : ℝ≥0∞)) =
       (⨅ j : ℕ, if g (τ j) < -H ω then (τ j : ℝ≥0∞) else ⊤)) := by
  dsimp only
  constructor
  · exact rightInterval_upper_strictExit_eq_schedule
      (fun t => X.X (b + t) ω - X.X b ω) (a - H ω)
      (levy_shiftedUpper_strictCrossing_rightInterval X ω b (a - H ω))
  · exact rightInterval_lower_strictExit_eq_schedule
      (fun t => X.X (b + t) ω - X.X b ω) (-H ω)
      (levy_shiftedLower_strictCrossing_rightInterval X ω b (-H ω))
