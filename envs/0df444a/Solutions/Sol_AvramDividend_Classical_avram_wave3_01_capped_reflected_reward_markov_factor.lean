-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_capped_reflected_reward_markov_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:33:24.113146+00:00
-- url     : https://prove2.me/submissions/585e783d-df34-441f-8848-7d662583b479

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- The actual capped first-record killed discount factors from the future
    Borel reflected-upcrossing reward by the source Lévy strong-Markov law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (N : ℝ≥0) (samples : ℕ → ℝ≥0) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let discount : ℝ≥0 → ℝ≥0∞ := fun t =>
       ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
     let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
       let ρ : ℝ≥0∞ := ⨅ i : ℕ,
         if c < f (samples i) - f 0 then
           (samples i : ℝ≥0∞) else ⊤
       let σ : ℝ≥0∞ := ⨅ i : ℕ,
         if f (samples i) - f 0 -
             (⨆ j : ℕ,
               if samples j ≤ samples i then
                 ENNReal.ofReal (f (samples j) - f 0)
               else 0).toReal < -a then
           (samples i : ℝ≥0∞) else ⊤
       if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
       else 0
     (∫⁻ ω, if ω ∈ A then discount (τ ω) *
       reward (fun t : ℝ≥0 =>
         X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
       (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω :=
    {ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω} ∩
    {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
  let discount : ℝ≥0 → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
  let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    let ρ : ℝ≥0∞ := ⨅ i : ℕ,
      if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
    let σ : ℝ≥0∞ := ⨅ i : ℕ,
      if f (samples i) - f 0 -
          (⨆ j : ℕ,
            if samples j ≤ samples i then
              ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a then
        (samples i : ℝ≥0∞) else ⊤
    if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0
  have hd : Measurable discount := by
    dsimp [discount]
    fun_prop
  have hr : Measurable reward := by
    exact avram_wave3_01_fresh_reflected_reward_measurable samples a c q
  change (∫⁻ ω, if ω ∈ A then discount (τ ω) *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) else 0 ∂P) =
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)
  simpa only [A, Set.mem_inter_iff, Set.mem_setOf_eq] using
    (levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
      X τ (firstRecord_truncation_stopping_rightCont X b N)
      A (firstRecord_capped_survival_in_finiteStoppedHistory X a b N)
      (firstRecord_capped_survival_measurable_global X a b N)
      (firstRecord_truncation_clock_measurable X b N)
      discount hd reward hr)
