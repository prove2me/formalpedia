-- Prove2me | solution 1 for AvramDividend.Classical.levy_stoppedHistory_truncated_scalar_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:21:21.05928+00:00
-- url     : https://prove2.me/submissions/879058a1-06d0-427a-ab16-eb9c3ab7fb03

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_min_const
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_continuousMeasurableReward_scalar_markov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The bounded Markov identity localises to an arbitrary stopping time on {τ ≤ T}. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T : ℝ≥0)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator (A ∩ {ω' : Ω | τ ω' ≤ T})
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P (A ∩ {ω' : Ω | τ ω' ≤ T}) *
      (∫⁻ y, g y ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
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
  have hsmall : ∀ ω, τT ω ≤ T := by
    intro ω
    exact min_le_right _ _
  have hbounded :=
    levy_boundedStopping_continuousMeasurableReward_scalar_markov
      X τT hstopT T hsmall B hBT g hg hgm C hbound hfin
  have hpath (ω : Ω) :
      Set.indicator B
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τT ω' + t) ω' - X.X (τT ω') ω')) ω =
      Set.indicator B
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω := by
    by_cases hω : ω ∈ B
    · have hτ : τ ω ≤ T := hω.2
      simp [Set.indicator, hω, τT, min_eq_left hτ]
    · simp [Set.indicator, hω]
  change (∫⁻ ω, Set.indicator B
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P B * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P))
  calc
    _ = ∫⁻ ω, Set.indicator B
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τT ω' + t) ω' - X.X (τT ω') ω')) ω ∂P := by
          apply lintegral_congr
          intro ω
          exact (hpath ω).symm
    _ = _ := hbounded
