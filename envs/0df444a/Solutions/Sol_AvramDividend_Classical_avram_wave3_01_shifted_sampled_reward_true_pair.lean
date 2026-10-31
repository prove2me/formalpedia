-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_shifted_sampled_reward_true_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:19:31.112261+00:00
-- url     : https://prove2.me/submissions/ada8f1ed-f89f-4481-8b81-0e951c6adc58

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Borel sampled future record and drawdown reward is exactly the
    true centred Lévy future-clock reward after an arbitrary finite shift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a c q : ℝ) (ω : Ω) (u : ℝ≥0) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let ρ : ℝ≥0∞ := ⨅ i : ℕ,
       if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ i : ℕ,
       if f (samples i) - f 0 -
         (⨆ j : ℕ, if samples j ≤ samples i
           then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
         then (samples i : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)
     let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
       f t - sSup (f '' Icc 0 t) < -a}, (i.1 : ℝ≥0∞)
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by
  classical
  have hp := avram_wave3_01_true_shifted_record_ruin_clock_pair X ω u a c
  have h := congrArg (fun z : ℝ≥0∞ × ℝ≥0∞ =>
    if z.1 < z.2 then ENNReal.ofReal (Real.exp (-(q * z.1.toReal)))
    else 0) hp
  have hz : X.X (u + 0) ω - X.X u ω = 0 := by simp
  simpa [hz] using h.symm
