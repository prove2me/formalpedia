-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_stopped_bounded_variable_signed_mark_grid_expected_zero_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:41:35.731013+00:00
-- url     : https://prove2.me/submissions/9dd5c554-79d9-4428-b8fd-2d08d9e9d933

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_stopped_variable_simplemark_predictable_finite_grid_budget_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Actual physical compensated simple marks with stopped predictable bounded finite-grid weights. -/
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
    (K : ι → ℝ)
    (hBound : ∀ i ∈ F, ∀ ω, ‖H i ω‖ ≤ K i)
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
    Integrable (fun ω => ∑ i ∈ F, W i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, W i ω * G i ω ∂P) = 0 := by
  classical
  intro NX B G W
  have hGI (i : ι) (hi : i ∈ F) : Integrable (G i) P := by
    simpa only [G, NX, B] using
      (avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
        X (s i) (t i) (hst i hi).le (S i)
        (hS i hi) (hNeg i hi) (hν i hi) (g i))
  have hWMeas (i : ι) (hi : i ∈ F) :
      StronglyMeasurable (W i) := by
    have hSet : MeasurableSet[𝓕.rightCont (s i)]
        {ω | τ ω ≤ (s i : WithTop ℝ≥0)} := hStop (s i)
    have hAt : StronglyMeasurable[𝓕.rightCont (s i)] (W i) := by
      simpa only [W] using
        (stronglyMeasurable_const :
          StronglyMeasurable[𝓕.rightCont (s i)] (fun _ : Ω => (0 : ℝ))).ite
          hSet (hH i hi)
    exact hAt.mono (𝓕.rightCont.le (s i))
  have hWI : ∀ i ∈ F, Integrable (fun ω => W i ω * G i ω) P := by
    intro i hi
    have hK (ω : Ω) : 0 ≤ K i :=
      (norm_nonneg (H i ω)).trans (hBound i hi ω)
    have hMeas : AEStronglyMeasurable
        (fun ω => W i ω * G i ω) P :=
      (hWMeas i hi).aestronglyMeasurable.mul (hGI i hi).aestronglyMeasurable
    refine Integrable.mono' ((hGI i hi).norm.const_mul (K i)) hMeas ?_
    apply Filter.Eventually.of_forall
    intro ω
    have hW : ‖W i ω‖ ≤ K i := by
      by_cases hτ : τ ω ≤ (s i : WithTop ℝ≥0)
      · change ‖(if τ ω ≤ (s i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)‖ ≤ K i
        simpa only [if_pos hτ, norm_zero] using hK ω
      · change ‖(if τ ω ≤ (s i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω)‖ ≤ K i
        simpa only [if_neg hτ] using hBound i hi ω
    calc
      ‖W i ω * G i ω‖ = ‖W i ω‖ * ‖G i ω‖ := norm_mul _ _
      _ ≤ K i * ‖G i ω‖ :=
        mul_le_mul_of_nonneg_right hW (norm_nonneg _)
  simpa only [NX, B, G, W] using
    (avram_oai_original_physical_stopped_variable_simplemark_predictable_finite_grid_budget_20261122
      X F s t hst S hS hNeg hν g H hH τ hStop hWI)
