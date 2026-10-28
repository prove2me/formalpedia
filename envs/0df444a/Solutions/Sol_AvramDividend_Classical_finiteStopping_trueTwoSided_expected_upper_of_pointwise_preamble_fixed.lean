-- Prove2me | solution 1 for AvramDividend.Classical.finiteStopping_trueTwoSided_expected_upper_of_pointwise_preamble_fixed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:44:22.889019+00:00
-- url     : https://prove2.me/submissions/a1d404b3-47b8-4041-bf25-2b5a1c6a6d34

import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_levy_trueTwoSided_discount_reward_eq_countable_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

/-! Transport finite-stopping Markov factorisation to the exact two-sided exit reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : MeasurableSet[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] A)
    (hAfine : MeasurableSet A) (hτfine : Measurable τ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (q upper lower : ℝ) (weight : Ω → ℝ≥0∞)
    (hUpper : ∀ ω : Ω, weight ω ≤
      (if ω ∈ A then discount (τ ω) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
         let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let up : ℝ≥0∞ := ⨅ j : ℕ, if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
         let dn : ℝ≥0∞ := ⨅ j : ℕ, if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
         if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
       else 0)) :
    (∫⁻ ω, weight ω ∂P) ≤
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                    (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) := by
  let grid : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun g =>
    let up : ℝ≥0∞ := ⨅ j : ℕ, if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
    let dn : ℝ≥0∞ := ⨅ j : ℕ, if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
    if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0
  have hr : Measurable reward :=
    countable_future_twoSided_discount_reward_measurable grid q upper lower
  have hStep := stoppedMarkov_pointwise_record_upper_to_expectation_rightCont
    X τ hτ A hA hAfine hτfine discount hd reward hr weight
    (by simpa only [reward, grid] using hUpper)
  have hReward :
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) =
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                      (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp (-(q *
            ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    simpa only [reward, grid, iInf_subtype] using
      (levy_trueTwoSided_discount_reward_eq_countable_schedule
        X ω q upper lower).symm
  rw [hReward] at hStep
  exact hStep