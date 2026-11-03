-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_gaussian_condExp_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:06:03.328597+00:00
-- url     : https://prove2.me/submissions/593a4295-1a3f-4c8a-8ed2-15e89dd8710a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original X-minus-jumps Gaussian stopped conditional mean and exact sigma squared variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : Ω → ℝ := fun ω =>
      M (τ ω + h) ω - M (τ ω) ω
    Integrable V P ∧
      (P[V | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ))) ∧
      Integrable (fun ω => V ω ^ 2) P ∧
      (P[(fun ω => V ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
  let W : Ω → ℝ := fun ω =>
    Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c
  have hM : ∀ t : ℝ≥0, ∀ ω : Ω,
      M t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro t ω
    dsimp [M]
    rw [hSourceDecomp t ω]
    ring
  have hV : ∀ ω : Ω, V ω = W ω := by
    intro ω
    dsimp [V, W]
    rw [hM (τ ω + h) ω, hM (τ ω) ω]
    push_cast
    ring
  have hFun : V = W := by
    funext ω
    exact hV ω
  have hOne :=
    avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
      Y hYν τ hτ B hbounded h
  dsimp only at hOne
  change Integrable V P ∧
    (P[V | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => V ω ^ 2) P ∧
    (P[(fun ω => V ω ^ 2) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2))
  rw [hFun]
  simpa only [hYσ] using hOne
