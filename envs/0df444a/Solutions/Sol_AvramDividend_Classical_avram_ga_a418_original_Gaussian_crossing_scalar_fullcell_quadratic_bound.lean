-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a418_original_Gaussian_crossing_scalar_fullcell_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:36:53.212552+00:00
-- url     : https://prove2.me/submissions/172fa16c-a1b1-4bfe-b371-4d73bbc11ba5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a396_original_crossing_compact_C2_generator_coefficients
import Theorems.Thm_AvramDividend_Classical_avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

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
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        s < ρ ω →
          |Real.exp (-(q * (s : ℝ))) *
              (deriv w y * z + (iteratedDeriv 2 w y / 2) *
                (z^2 - (Δ : ℝ) * X.σ^2)) +
            (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
              X.generator w y| ≤
          K * (|z| + z^2 + (Δ : ℝ)) := by
  obtain ⟨M,hM,hCoeffs⟩ :=
    avram_ga_a396_original_crossing_compact_C2_generator_coefficients
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  let a : ℝ := X.σ^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let K : ℝ := M * (2 + a)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  filter_upwards [hCoeffs] with ω hω
  intro m i Δ s y z hs
  have hδ : 0 ≤ (Δ : ℝ) := (Δ).property
  have hE0 : 0 ≤ Real.exp (-(q * (s : ℝ))) := Real.exp_nonneg _
  have hE1 : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := (s).property
    nlinarith [mul_nonneg (le_of_lt hq) hs0]
  have hh := hω m i
  have hcoef : |deriv w y| ≤ M ∧
        |iteratedDeriv 2 w y| ≤ M ∧
        |X.generator w y| ≤ M := by
    simpa only [y,s,Δ] using hh hs
  have hscalar := avram_ga_a398_scalar_Gaussian_HJB_fullcell_absolute_budget
    M a (Real.exp (-(q * (s : ℝ)))) (Δ : ℝ) z
    (deriv w y) (iteratedDeriv 2 w y)
    (X.generator w y) hM ha hE0 hE1 hδ
    hcoef.1 hcoef.2.1 hcoef.2.2
  simpa only [K,a] using hscalar
