-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_scalar_markov_no_meas_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:25:03.42302+00:00
-- url     : https://prove2.me/submissions/8e282862-e7ee-4766-b3db-90b3676fd32a

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_min_const
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFutureReward_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_boundedReward_scalar_markov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The full finite-time Lévy strong-Markov scalar law needs no additional measurability assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  have hmeas (n : ℕ) : Measurable
      (Set.indicator (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)})
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τ ω' + t) ω' - X.X (τ ω') ω'))) := by
    let T : ℝ≥0 := n
    let τT : Ω → ℝ≥0 := fun ω => min (τ ω) T
    let B : Set Ω := A ∩ {ω : Ω | τ ω ≤ T}
    have hstopT : IsStoppingTime 𝓕
        (fun ω => (τT ω : WithTop ℝ≥0)) := by
      simpa only [τT, WithTop.coe_min] using
        (IsStoppingTime.min_const hstop T)
    have hBT : ∀ s : ℝ≥0,
        MeasurableSet[𝓕 s]
          (B ∩ {ω : Ω | τT ω ≤ s}) := by
      intro s
      exact stoppedHistory_event_min_const 𝓕 τ A hA T s
    have hsmall : ∀ ω, τT ω ≤ T := fun ω => min_le_right _ _
    have hM := levy_boundedStopping_stoppedFutureReward_measurable
      X τT hstopT T hsmall B hBT g hg hgm
    have heq : (Set.indicator B
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τ ω' + t) ω' - X.X (τ ω') ω'))) =
      (Set.indicator B
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τT ω' + t) ω' - X.X (τT ω') ω'))) := by
      funext ω
      by_cases hω : ω ∈ B
      · have hτ : τ ω ≤ T := hω.2
        simp [Set.indicator, hω, τT, min_eq_left hτ]
      · simp [Set.indicator, hω]
    change Measurable (Set.indicator B
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')))
    rw [heq]
    exact hM
  exact levy_finiteStopping_boundedReward_scalar_markov
    X τ hstop A hA g hg hgm C hbound hfin hmeas
