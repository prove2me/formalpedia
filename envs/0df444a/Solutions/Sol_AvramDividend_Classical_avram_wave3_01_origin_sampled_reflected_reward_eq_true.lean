-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_origin_sampled_reflected_reward_eq_true
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:27:54.733089+00:00
-- url     : https://prove2.me/submissions/b6b5ca11-f454-4ba4-9aca-fd98f9a7ce7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Borel sampled future-path reward at the source origin is exactly
    the actual discounted reflected-killed first-record payoff, pointwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a c q : ℝ) (ω : Ω) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let f : ℝ≥0 → ℝ := fun t => X.X t ω
     let ρ : ℝ≥0∞ := ⨅ i : ℕ,
       if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ i : ℕ,
       if f (samples i) - f 0 -
         (⨆ j : ℕ, if samples j ≤ samples i
           then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
         then (samples i : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
     else 0) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let f : ℝ≥0 → ℝ := fun t => X.X t ω
  let ρ : ℝ≥0∞ := ⨅ i : ℕ,
    if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
  let σ : ℝ≥0∞ := ⨅ i : ℕ,
    if f (samples i) - f 0 -
      (⨆ j : ℕ, if samples j ≤ samples i
        then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
      then (samples i : ℝ≥0∞) else ⊤
  change (if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
    else 0) =
    (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
    else 0)
  have hzero : X.X 0 ω = 0 := X.X_zero ω
  have hp := avram_wave3_01_true_shifted_record_ruin_clock_pair
    X ω 0 a c
  dsimp at hp
  simp only [zero_add, hzero, sub_zero] at hp
  have hρ : ρ = twoSidedExitUpTime X c ω := by
    simpa [ρ, f, samples, twoSidedExitUpTime, zero_add, hzero, iInf_subtype] using
      (congrArg Prod.fst hp).symm
  have hσ : σ = barrierRuinTime X a ω := by
    calc
      σ = (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
          (i.1 : ℝ≥0∞)) := by
        simpa only [σ, f, samples] using
          (avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
            X ω a).symm
      _ = barrierRuinTime X a ω :=
        (avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
          X a ω).symm
  rw [hρ, hσ]
