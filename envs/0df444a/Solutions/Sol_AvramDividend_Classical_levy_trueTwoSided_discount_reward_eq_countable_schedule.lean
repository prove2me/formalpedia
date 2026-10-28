-- Prove2me | solution 1 for AvramDividend.Classical.levy_trueTwoSided_discount_reward_eq_countable_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:03:49.611004+00:00
-- url     : https://prove2.me/submissions/0040811e-4d88-45d3-96e8-8edc0ef5449c

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_strictLower_exit_subtype_inf_eq_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Exact two-sided killed reward is represented by a Borel countable path schedule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q upper lower : ℝ) :
    (let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < X.X t ω},
      (i.1 : ℝ≥0∞)
     let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // X.X t ω < lower},
      (i.1 : ℝ≥0∞)
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (let τ : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ j : ℕ,
       if upper < X.X (τ j) ω then (τ j : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ j : ℕ,
       if X.X (τ j) ω < lower then (τ j : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by
  classical
  dsimp only
  rw [levy_strictUpper_exit_subtype_inf_eq_schedule X ω upper,
      levy_strictLower_exit_subtype_inf_eq_schedule X ω lower]
  rfl
