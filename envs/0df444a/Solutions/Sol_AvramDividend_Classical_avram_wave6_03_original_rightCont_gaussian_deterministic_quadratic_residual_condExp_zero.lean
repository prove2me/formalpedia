-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:50:37.514784+00:00
-- url     : https://prove2.me/submissions/d337d6bb-c601-46b1-ae91-3718ad034379

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact integrable original-source conditional Gaussian quadratic residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable (fun ω => Y ω ^ 2 - ((t - s) : ℝ) * X.σ ^ 2) P ∧
      (P[(fun ω => Y ω ^ 2 - ((t - s) : ℝ) * X.σ ^ 2) |
          𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
  let a : ℝ := ((t - s) : ℝ) * X.σ ^ 2
  let V : Ω → ℝ := fun ω => Y ω ^ 2
  let A : Ω → ℝ := fun _ => a
  have hVarPair :=
    avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance
      X hν s t hst
  have hVI : Integrable V P := hVarPair.1
  have hVCE : P[V | 𝓕.rightCont s] =ᵐ[P] A := hVarPair.2
  have hAI : Integrable A P := integrable_const a
  have hACE : P[A | 𝓕.rightCont s] = A :=
    condExp_of_stronglyMeasurable ((𝓕.rightCont).le s)
      stronglyMeasurable_const hAI
  have hQI : Integrable (V - A) P := hVI.sub hAI
  have hQCE : P[V - A | 𝓕.rightCont s] =ᵐ[P]
      P[V | 𝓕.rightCont s] - P[A | 𝓕.rightCont s] :=
    condExp_sub hVI hAI (𝓕.rightCont s)
  change Integrable (V - A) P ∧
    (P[V - A | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)))
  refine ⟨hQI, ?_⟩
  filter_upwards [hQCE, hVCE] with ω hq hv
  calc
    (P[V - A | 𝓕.rightCont s]) ω =
        (P[V | 𝓕.rightCont s] - P[A | 𝓕.rightCont s]) ω := hq
    _ = (P[V | 𝓕.rightCont s]) ω - (P[A | 𝓕.rightCont s]) ω := rfl
    _ = A ω - A ω := by rw [hv, hACE]
    _ = 0 := sub_self _
