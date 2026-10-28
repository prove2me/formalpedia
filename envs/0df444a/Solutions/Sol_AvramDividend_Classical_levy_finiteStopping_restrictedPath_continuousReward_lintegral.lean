-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_restrictedPath_continuousReward_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:44:50.165594+00:00
-- url     : https://prove2.me/submissions/ee85bab3-83a7-4cd8-8efb-23e516fd6bc7

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_scalar_markov_no_meas_premise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The stopped-history restricted future-path law factors on continuous tests. -/
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
    (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) (P.restrict A))) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  let shift : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hshift : Measurable shift :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  have hSet : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  change (∫⁻ y, g y ∂(Measure.map shift (P.restrict A))) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P))
  calc
    (∫⁻ y, g y ∂(Measure.map shift (P.restrict A))) =
        ∫⁻ ω, g (shift ω) ∂(P.restrict A) :=
      lintegral_map hgm hshift
    _ = ∫⁻ ω, Set.indicator A (fun ω => g (shift ω)) ω ∂P :=
      (lintegral_indicator hSet (fun ω => g (shift ω))).symm
    _ = P A * (∫⁻ y, g y ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
      simpa only [shift] using
        (levy_finiteStopping_scalar_markov_no_meas_premise
          X τ hstop A hA g hg hgm C hbound hfin)
