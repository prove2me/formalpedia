-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_restrictedFuturePath_mapLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:52:31.139783+00:00
-- url     : https://prove2.me/submissions/447d573f-6119-42f9-8c55-4fb86755aa5b

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFDD_mapLaw
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full stopped future-path law under a stopped-history event is the scaled original Lévy law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    Measure.map
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) (P.restrict A) =
    (P A) • Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
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
  have hMass : (Measure.map Y (P.restrict A)) Set.univ ≠ ⊤ := by
    rw [Measure.map_apply hY MeasurableSet.univ]
    exact measure_ne_top (P.restrict A) Set.univ
  change Measure.map Y (P.restrict A) =
    (P A) • Measure.map Z P
  apply scaled_piPathMeasure_eq_of_finite_pushforwards
    Y Z hY hZ (P A) hMass
  intro J
  exact levy_finiteStopping_restrictedFDD_mapLaw X τ hstop A hA J
