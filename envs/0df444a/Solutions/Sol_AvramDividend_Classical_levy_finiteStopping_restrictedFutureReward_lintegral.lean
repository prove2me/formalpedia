-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_restrictedFutureReward_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:00:54.428229+00:00
-- url     : https://prove2.me/submissions/1577d4f6-b2c0-42bd-89bc-f575ca50e899

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_restrictedPathLaw_scalar_lintegral_reward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every measurable nonnegative reward of the stopped future path factors across a stopped-history event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator A
      (fun ω' => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ ω, g (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hY : Measurable Y :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hSet : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  have hLaw : Measure.map Y (P.restrict A) =
      (P A) • Measure.map Z P := by
    simpa only [Y, Z] using
      (levy_finiteStopping_restrictedFuturePath_mapLaw
        X τ hstop A hA)
  have hReward :=
    restrictedPathLaw_scalar_lintegral_reward
      P A hSet Y hY (Measure.map Z P) hLaw g hg
  rw [lintegral_map hg hZ] at hReward
  simpa only [Y, Z] using hReward
