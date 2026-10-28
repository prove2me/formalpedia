-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_restrictedFDD_compactTest_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:18:20.197148+00:00
-- url     : https://prove2.me/submissions/63f451f8-f897-4e51-a392-3cf64129e056

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable
import Theorems.Thm_AvramDividend_Classical_compactTest_nnreal_uniformBound_finiteLintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Stopped-history restricted finite-coordinate laws factor on all compact NNReal tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (hP : P Set.univ ≠ ⊤)
    (J : Finset ℝ≥0)
    (f : CompactlySupportedContinuousMap (J → ℝ) ℝ≥0) :
    (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(Measure.map
      (fun ω : Ω => fun j : J =>
        X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω) (P.restrict A))) =
    P A * (∫⁻ y, ((f (fun j : J => y (j : ℝ≥0)) : ℝ≥0) : ℝ≥0∞)
      ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  let h : (J → ℝ) → ℝ≥0∞ := fun z => ((f z : ℝ≥0) : ℝ≥0∞)
  have hcont : Continuous h := ENNReal.continuous_coe.comp f.continuous
  have hhm : Measurable h := hcont.measurable
  let C : ℝ≥0∞ :=
    ((nndist (0 : BoundedContinuousFunction (J → ℝ) ℝ≥0)
      f.toBoundedContinuousFunction : ℝ≥0) : ℝ≥0∞)
  have henv := compactTest_nnreal_uniformBound_finiteLintegral P hP f
  have hb : ∀ z, h z ≤ C := henv.1
  have hf : (∫⁻ _ : Ω, C ∂P) ≠ ⊤ := henv.2
  let future : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hfuture : Measurable future :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  let futureJ : Ω → (J → ℝ) := fun ω j => future ω (j : ℝ≥0)
  have hfutureJ : Measurable futureJ := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply (j : ℝ≥0)).comp hfuture
  have hSet : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  calc
    (∫⁻ z, ((f z : ℝ≥0) : ℝ≥0∞) ∂(Measure.map
        (fun ω : Ω => fun j : J =>
          X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω) (P.restrict A))) =
        ∫⁻ ω, h (futureJ ω) ∂(P.restrict A) := by
      change (∫⁻ z, h z ∂(Measure.map futureJ (P.restrict A))) =
        ∫⁻ ω, h (futureJ ω) ∂(P.restrict A)
      exact lintegral_map hhm hfutureJ
    _ = ∫⁻ ω, Set.indicator A (fun ω' => h (futureJ ω')) ω ∂P := by
      exact (lintegral_indicator hSet (fun ω => h (futureJ ω))).symm
    _ = P A * (∫⁻ y, ((f (fun j : J => y (j : ℝ≥0)) : ℝ≥0) : ℝ≥0∞)
        ∂(Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
      simpa only [h, futureJ, future] using
        (levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
          X τ hstop A hA J h hcont hhm C hb hf)
