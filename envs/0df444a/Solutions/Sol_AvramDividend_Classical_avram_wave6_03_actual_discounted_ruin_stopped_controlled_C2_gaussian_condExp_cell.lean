-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_condExp_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:46:38.482199+00:00
-- url     : https://prove2.me/submissions/27edf812-0f6b-415e-9076-7a3ae244dbd4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_cell_chain_rule
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_discounted_controlled_hessian_stopped_history_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Conditional Gaussian Taylor cell for the original bounded stopped dividend reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hGbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K₁)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K₂) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    Integrable (fun ω => G ω * Y ω) P ∧
    Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
    (P[(fun ω => G ω * Y ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    (P[(fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2 / 2) * H ω)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hCell := avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_cell_chain_rule
    X hν x D hD w C hw q T τ hτ B hbounded h K₁ hK₁ hGbound K₂ hK₂ hHbound
  change Integrable (fun ω => G ω * Y ω) P ∧
    (∫ ω, G ω * Y ω ∂P) = 0 ∧
    Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P) at hCell
  have hMom := avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
    X hν τ hτ B hbounded h
  change Integrable Y P ∧
    (P[Y | hstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => Y ω ^ 2) P ∧
    (P[(fun ω => Y ω ^ 2) | hstop.measurableSpace]
      =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) at hMom
  have hGstop : Measurable[hstop.measurableSpace] G :=
    measurable_stoppedValue ((avram_wave3_04_source_stopped_discounted_deriv_predictable
      X x D hD w q T).isStronglyProgressive) hstop
  have hHstop : Measurable[hstop.measurableSpace] H :=
    avram_wave6_03_original_discounted_controlled_hessian_stopped_history_measurable X x D hD w C hw q T τ hstop
  have hPullG : P[(fun ω => G ω * Y ω) | hstop.measurableSpace] =ᵐ[P]
      G * P[Y | hstop.measurableSpace] :=
    condExp_mul_of_stronglyMeasurable_left hGstop.stronglyMeasurable hCell.1 hMom.1
  let K : Ω → ℝ := fun ω => (1 / 2 : ℝ) * H ω
  have hKstop : Measurable[hstop.measurableSpace] K := measurable_const.mul hHstop
  have hKYI : Integrable (K * (fun ω => Y ω ^ 2)) P := by
    convert hCell.2.2.1 using 1
    funext ω
    simp only [Pi.mul_apply, K]
  have hPullH : P[K * (fun ω => Y ω ^ 2) | hstop.measurableSpace] =ᵐ[P]
      K * P[(fun ω => Y ω ^ 2) | hstop.measurableSpace] :=
    condExp_mul_of_stronglyMeasurable_left hKstop.stronglyMeasurable hKYI hMom.2.2.1
  have hCEG : P[(fun ω => G ω * Y ω) | hstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    filter_upwards [hPullG, hMom.2.1] with ω hp hz
    calc
      (P[(fun ω => G ω * Y ω) | hstop.measurableSpace]) ω =
          (G * P[Y | hstop.measurableSpace]) ω := hp
      _ = G ω * (P[Y | hstop.measurableSpace]) ω := rfl
      _ = 0 := by rw [hz]; ring
  have hCEH : P[(fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) | hstop.measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2 / 2) * H ω) := by
    filter_upwards [hPullH, hMom.2.2.2] with ω hp hz
    calc
      (P[(fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
        hstop.measurableSpace]) ω =
        (K * P[(fun ω => Y ω ^ 2) | hstop.measurableSpace]) ω := hp
      _ = K ω * (P[(fun ω => Y ω ^ 2) | hstop.measurableSpace]) ω := rfl
      _ = K ω * ((h : ℝ) * X.σ ^ 2) := by rw [hz]
      _ = ((h : ℝ) * X.σ ^ 2 / 2) * H ω := by dsimp [K]; ring
  change Integrable (fun ω => G ω * Y ω) P ∧
    Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
    (P[(fun ω => G ω * Y ω) | hstop.measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    (P[(fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
      hstop.measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2 / 2) * H ω))
  exact ⟨hCell.1, hCell.2.2.1, hCEG, hCEH⟩
