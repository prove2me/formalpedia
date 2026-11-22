-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_physical_stopped_variable_simplemark_predictable_finite_grid_budget_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:25:18.564633+00:00
-- url     : https://prove2.me/submissions/1fb6ea58-c166-43d0-bd91-458ce5743aee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ F, s i < t i)
    (S : ι → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hNeg : ∀ i ∈ F, S i ⊆ Iio (0 : ℝ))
    (hν : ∀ i ∈ F, X.ν (S i) < ⊤)
    (g : ι → SimpleFunc ℝ ℝ)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ F,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ι → ℝ → Set ℝ := fun i y => S i ∩ (g i) ⁻¹' {y}
    let G : ι → Ω → ℝ := fun i ω =>
      ∑ y ∈ (g i).range, y *
        ((NX ω (Ioc (s i) (t i) ×ˢ B i y)).toReal -
          ((((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i y))).toReal)
    let W : ι → Ω → ℝ := fun i ω =>
      if τ ω ≤ (s i : WithTop ℝ≥0)
        then 0 else H i ω
    (∀ i ∈ F, Integrable (fun ω => W i ω * G i ω) P) →
      Integrable (fun ω => ∑ i ∈ F, W i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, W i ω * G i ω ∂P) = 0  := by
  classical
  intro NX B G W hWI
  have hWMeas : ∀ i ∈ F,
      StronglyMeasurable[𝓕.rightCont (s i)] (W i) := by
    intro i hi
    simpa only [W] using
      (avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
        𝓕 τ hStop (s i) (H i) (hH i hi))
  simpa only [NX, B, G, W] using
    (avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
      X F s t hst S hS hNeg hν g W hWMeas hWI)
