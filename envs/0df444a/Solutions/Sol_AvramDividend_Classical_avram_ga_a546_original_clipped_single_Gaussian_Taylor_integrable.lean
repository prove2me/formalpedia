-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a546_original_clipped_single_Gaussian_Taylor_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:56:16.403299+00:00
-- url     : https://prove2.me/submissions/e845c715-2d88-47bd-bbf8-e463224ab0df

import Theorems.Thm_AvramDividend_Classical_avram_ga_a550_original_Taylor_cell_AEStronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a548_quadratic_Gaussian_Taylor_coefficient_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a545_integrable_of_quadratic_gaussian_envelope
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      if 0 < ρ ω ∧ s < ρ ω then
        E s * (deriv w (Y s) * z +
          (iteratedDeriv 2 w (Y s) / 2) *
            (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
    ∀ m i : ℕ, i < m → Integrable (B m i) P := by
  classical
  intro B m i hi
  letI : IsProbabilityMeasure P := X.isProbability
  have hMeas := avram_ga_a550_original_Taylor_cell_AEStronglyMeasurable
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen
    x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m i hi
  change AEStronglyMeasurable (B m i) P at hMeas
  obtain ⟨M,hM,hjet⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD.1.1 w C hTopCap hw_smooth ρ j hprefix
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  let z : Ω → ℝ := fun ω =>
    X.X (s+Δ) ω - X.X s ω - (Δ : ℝ)*X.c
  have hzI := avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
    X hNuZero n m i hi
  change Integrable (fun ω => (z ω)^2) P at hzI
  let C0 : ℝ := M*(2+(Δ : ℝ)*X.σ^2)
  have hC0 : 0 ≤ C0 := by positivity
  have hBound : ∀ᵐ ω ∂P,
      |B m i ω| ≤ C0*(1+(z ω)^2) := by
    filter_upwards [hjet] with ω hw
    by_cases ha : 0 < ρ ω ∧ s < ρ ω
    · let y : ℝ := x + X.X s ω - rightLimit D s ω
      have hder : |deriv w y| ≤ M := (hw s ha.2).2.1
      have hder2 : |iteratedDeriv 2 w y| ≤ M := by
        simpa [iteratedDeriv_succ, iteratedDeriv_one] using
          (hw s ha.2).2.2
      have hs0 : 0 ≤ (Δ : ℝ)*X.σ^2 := by positivity
      have hpoly := avram_ga_a548_quadratic_Gaussian_Taylor_coefficient_absolute_bound
        M (deriv w y) (iteratedDeriv 2 w y) (z ω)
        ((Δ : ℝ)*X.σ^2) hM hs0 hder hder2
      let E : ℝ := Real.exp (-(q * (s : ℝ)))
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (mul_nonneg hq.le (by positivity)))
      have hEq : B m i ω =
          E*(deriv w y*z ω + iteratedDeriv 2 w y/2*
            ((z ω)^2 - (Δ : ℝ)*X.σ^2)) := by
        simp [B, Δ, s, z, y, E, ha]
      rw [hEq, abs_mul, abs_of_nonneg hE0]
      calc
        E*|deriv w y*z ω + iteratedDeriv 2 w y/2*
          ((z ω)^2 - (Δ : ℝ)*X.σ^2)| ≤
            |deriv w y*z ω + iteratedDeriv 2 w y/2*
              ((z ω)^2 - (Δ : ℝ)*X.σ^2)| :=
          mul_le_of_le_one_left (abs_nonneg _) hE1
        _ ≤ C0*(1+(z ω)^2) := hpoly
    · have hzero : B m i ω = 0 := by simp [B, Δ, s, ha]
      rw [hzero, abs_zero]
      exact mul_nonneg hC0 (by positivity)
  exact avram_ga_a545_integrable_of_quadratic_gaussian_envelope
    (B m i) z C0 hC0 hMeas hzI hBound
