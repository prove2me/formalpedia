-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a537_original_Taylor_cell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:07:22.724961+00:00
-- url     : https://prove2.me/submissions/e16a482e-0f4e-4285-a435-ebf539e3dcfb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a396_original_crossing_compact_C2_generator_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a550_original_Taylor_cell_AEStronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a551_quadratic_domination_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a552_gaussian_centered_Taylor_algebra_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let B : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      if 0 < ρ ω ∧ s < ρ ω then E s * (deriv w (Y s) * z +
        (iteratedDeriv 2 w (Y s) / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    ∀ m i : ℕ, i < m →
      Integrable (B m i) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro B m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let z : Ω → ℝ := fun ω =>
    X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
  obtain ⟨K,hK,hCoeff⟩ :=
    avram_ga_a396_original_crossing_compact_C2_generator_coefficients
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  let δ : ℝ := (Δ : ℝ) * X.σ ^ 2
  let R : ℝ := K * (2 + δ)
  have hδ : 0 ≤ δ := mul_nonneg (by positivity) (sq_nonneg _)
  have hR : 0 ≤ R := mul_nonneg hK (by dsimp [δ]; positivity)
  have hz2 : Integrable (fun ω => (z ω)^2) P := by
    simpa only [z, s, Δ] using
      (avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
        X hNuZero n m i hi)
  have hMeas :=
    avram_ga_a550_original_Taylor_cell_AEStronglyMeasurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m i hi
  have hBound : ∀ᵐ ω ∂P, |B m i ω| ≤ R * (1 + (z ω)^2) := by
    filter_upwards [hCoeff] with ω hc
    by_cases hs : 0 < ρ ω ∧ s < ρ ω
    · have hc0 := (hc m i hs.2).1
      have hc1 := (hc m i hs.2).2.1
      have he0 : 0 ≤ Real.exp (-(q * (s : ℝ))) := (Real.exp_pos _).le
      have he1 : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
        apply (Real.exp_le_one_iff).2
        exact neg_nonpos.mpr (mul_nonneg hq.le (by positivity))
      have hb := avram_ga_a552_gaussian_centered_Taylor_algebra_bound
        (deriv w (x + X.X s ω - rightLimit D s ω))
        (iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω))
        (z ω) (Real.exp (-(q * (s : ℝ)))) K δ hK hδ
        hc0 hc1 he0 he1
      simpa only [B, R, z, s, Δ, δ, if_pos hs] using hb
    · have hs' : ¬ (0 < ρ ω ∧ (i : ℝ≥0) * Δ < ρ ω) := by
        simpa only [s] using hs
      have hzero : B m i ω = 0 := by
        simp [B, Δ, hs']
      have hnonneg : 0 ≤ R * (1 + (z ω)^2) :=
        mul_nonneg hR (by positivity)
      simpa only [hzero, abs_zero] using hnonneg
  exact avram_ga_a551_quadratic_domination_integrable
    (B m i) z R hR hMeas hz2 (integrable_const R) hBound
