-- Prove2me | solution 1 for AvramDividend.Classical.finiteStopping_trueTwoSided_expected_lower_imported
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:02:06.637842+00:00
-- url     : https://prove2.me/submissions/0193ae58-d36f-49db-870c-aae0f656862c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.CompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_stoppedMarkov_pointwise_record_lower_to_expectation_rightCont
import Theorems.Thm_AvramDividend_Classical_countable_future_twoSided_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_levy_trueTwoSided_discount_reward_eq_countable_schedule
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

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
    (hLower : ∀ ω : Ω,
      (if ω ∈ A then discount (τ ω) *
        (let g : ℝ≥0 → ℝ := fun t => X.X (τ ω + t) ω - X.X (τ ω) ω
         let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
         let up : ℝ≥0∞ := ⨅ j : ℕ, if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
         let dn : ℝ≥0∞ := ⨅ j : ℕ, if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
         if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0)
       else 0) ≤ weight ω) :
    (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                    (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) ≤
    (∫⁻ ω, weight ω ∂P) := by
  let grid : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
    (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun g =>
    let up : ℝ≥0∞ := ⨅ j : ℕ, if upper < g (grid j) then (grid j : ℝ≥0∞) else ⊤
    let dn : ℝ≥0∞ := ⨅ j : ℕ, if g (grid j) < lower then (grid j : ℝ≥0∞) else ⊤
    if up < dn then ENNReal.ofReal (Real.exp (-(q * up.toReal))) else 0
  have hr : Measurable reward :=
    countable_future_twoSided_discount_reward_measurable grid q upper lower
  have hL : ∀ ω, (if ω ∈ A then discount (τ ω) *
      reward (fun t => X.X (τ ω + t) ω - X.X (τ ω) ω) else 0) ≤ weight ω := by
    simpa only [reward, grid] using hLower
  have hM := stoppedMarkov_pointwise_record_lower_to_expectation_rightCont
    X τ hτ A hA hAfine hτfine discount hd reward hr weight hL
  have hEq : (∫⁻ ω, reward (fun t => X.X t ω) ∂P) =
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
                      (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) := by
    apply lintegral_congr
    intro ω
    have hup :
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) =
        (⨅ i : {t : ℝ≥0 // upper < X.X t ω}, (i.1 : ℝ≥0∞)) := by
      exact (iInf_subtype (f := fun i : {t : ℝ≥0 // upper < X.X t ω} =>
        (i.1 : ℝ≥0∞))).symm
    have hdn :
        (⨅ (t : ℝ≥0) (_ : X.X t ω < lower), (t : ℝ≥0∞)) =
        (⨅ i : {t : ℝ≥0 // X.X t ω < lower}, (i.1 : ℝ≥0∞)) := by
      exact (iInf_subtype (f := fun i : {t : ℝ≥0 // X.X t ω < lower} =>
        (i.1 : ℝ≥0∞))).symm
    rw [hup, hdn]
    simpa only [reward, grid] using
      (levy_trueTwoSided_discount_reward_eq_countable_schedule X ω q upper lower).symm
  simpa only [hEq] using hM
