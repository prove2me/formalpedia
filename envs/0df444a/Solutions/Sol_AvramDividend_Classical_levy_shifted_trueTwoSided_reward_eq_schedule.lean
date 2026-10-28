-- Prove2me | solution 1 for AvramDividend.Classical.levy_shifted_trueTwoSided_reward_eq_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:20:38.852904+00:00
-- url     : https://prove2.me/submissions/07b8d839-c0f1-41f4-91c1-208b263a46df

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
import Theorems.Thm_AvramDividend_Classical_levy_shiftedLower_strictCrossing_rightInterval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Identify the stopped future-path reward with its measurable schedule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (q upper lower : ℝ) :
    (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t},
       (i.1 : ℝ≥0∞)
     let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower},
       (i.1 : ℝ≥0∞)
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let τ : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ j : ℕ,
       if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ j : ℕ,
       if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by
  classical
  dsimp only
  rw [rightInterval_upper_strictExit_eq_schedule
      (fun t : ℝ≥0 => X.X (u + t) ω - X.X u ω) upper
      (levy_shiftedUpper_strictCrossing_rightInterval X ω u upper),
      rightInterval_lower_strictExit_eq_schedule
      (fun t : ℝ≥0 => X.X (u + t) ω - X.X u ω) lower
      (levy_shiftedLower_strictCrossing_rightInterval X ω u lower)]
  rfl
