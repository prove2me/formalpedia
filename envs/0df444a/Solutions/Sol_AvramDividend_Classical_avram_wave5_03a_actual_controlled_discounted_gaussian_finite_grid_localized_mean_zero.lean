-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_finite_grid_localized_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:37:05.97006+00:00
-- url     : https://prove2.me/submissions/bce761f0-3dc7-4067-8d7c-062ab6acc852

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Genuine controlled strict-prepayment gradient, source right-continuous predictable Gaussian finite grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (q K θ : ℝ) (hK : 0 ≤ K) (hθ : 0 ≤ θ) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : ι → Ω → ℝ := fun i ω =>
      (Real.exp (-(q * (s i : ℝ))) * X.σ) *
        max (-K) (min K (G (s i) ω))
    (∫ ω, ∑ i ∈ S, H i ω *
      ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0 := by
  dsimp only
  classical
  let G : ℝ≥0 → Ω → ℝ := fun t ω =>
    let y := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
  let H : ι → Ω → ℝ := fun i ω =>
    (Real.exp (-(q * (s i : ℝ))) * X.σ) *
      max (-K) (min K (G (s i) ω))
  change (∫ ω, ∑ i ∈ S, H i ω *
    ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
      ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0
  have hG : IsStronglyPredictable 𝓕.rightCont G :=
    avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
      X x D hD w C hw
  obtain ⟨hClip, hClipBound⟩ :=
    avram_wave3_04_clipped_stronglyPredictable_bounded G hG K hK
  have hH :
      ∀ i ∈ S, StronglyMeasurable[𝓕.rightCont (s i)] (H i) := by
    intro i hi
    exact (hClip.stronglyAdapted (s i)).const_mul
      (Real.exp (-(q * (s i : ℝ))) * X.σ)
  have hBound :
      ∀ i ∈ S, ∀ ω,
        ‖H i ω‖ ≤
          ‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K := by
    intro i hi ω
    change ‖(Real.exp (-(q * (s i : ℝ))) * X.σ) *
      max (-K) (min K (G (s i) ω))‖ ≤
      ‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hClipBound (s i) ω) (norm_nonneg _)
  exact avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero
    X hν S s t hst H hH
      (fun i => ‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K)
      hBound θ hθ
