-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_restrictedFDD_mapLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:25:51.048988+00:00
-- url     : https://prove2.me/submissions/3327293d-e535-42a7-9716-0e59754b019d

import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_compactTest_lintegral
import Theorems.Thm_AvramDividend_Classical_compactTest_lintegral_scalar_factor_implies_measure_smul
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The finite-dimensional stopped-future law restricted to a stopped event is a scaled Lévy law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (J : Finset ℝ≥0) :
    Measure.map
      (fun ω : Ω => fun j : J =>
        X.X (τ ω + (j : ℝ≥0)) ω - X.X (τ ω) ω) (P.restrict A) =
    (P A) • Measure.map (fun ω : Ω => fun j : J =>
      X.X (j : ℝ≥0) ω) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let full : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hfull : Measurable full := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  let future : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  have hfuture : Measurable future :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  let Y : Ω → (J → ℝ) := fun ω j => future ω (j : ℝ≥0)
  let Z : Ω → (J → ℝ) := fun ω j => full ω (j : ℝ≥0)
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply (j : ℝ≥0)).comp hfuture
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply (j : ℝ≥0)).comp hfull
  haveI : (Measure.map Z P).Regular := inferInstance
  haveI : ((P A) • Measure.map Z P).Regular :=
    Measure.Regular.smul (measure_ne_top P A)
  change Measure.map Y (P.restrict A) = (P A) • Measure.map Z P
  apply compactTest_lintegral_scalar_factor_implies_measure_smul (P A)
  intro f
  let hf : (J → ℝ) → ℝ≥0∞ := fun z => ((f z : ℝ≥0) : ℝ≥0∞)
  have hfm : Measurable hf :=
    (ENNReal.continuous_coe.comp f.continuous).measurable
  let proj : (ℝ≥0 → ℝ) → (J → ℝ) :=
    fun y j => y (j : ℝ≥0)
  have hproj : Measurable proj := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (j : ℝ≥0)
  let g : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun y => hf (proj y)
  have hgm : Measurable g := hfm.comp hproj
  calc
    (∫⁻ z, hf z ∂(Measure.map Y (P.restrict A))) =
        P A * (∫⁻ y, g y ∂(Measure.map full P)) := by
      simpa only [hf, g, proj, full, Y, future] using
        (levy_finiteStopping_restrictedFDD_compactTest_lintegral
          X τ hstop A hA (measure_ne_top P Set.univ) J f)
    _ = P A * (∫⁻ ω, g (full ω) ∂P) := by
      rw [lintegral_map hgm hfull]
    _ = P A * (∫⁻ ω, hf (Z ω) ∂P) := rfl
    _ = P A * (∫⁻ z, hf z ∂(Measure.map Z P)) := by
      rw [lintegral_map hfm hZ]
