-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger50_original_clipped_gaussian_physical_Taylor_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:04:39.162215+00:00
-- url     : https://prove2.me/submissions/2bdc7df4-602f-4752-a368-94d8efa65d1b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger139_original_clipped_postpayment_discount_euler_absolute_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger140_original_clipped_postpayment_spatial_gaussian_Taylor_absolute_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger143_measurable_residual_two_absolute_L1_errors_glue_positive
import Theorems.Thm_AvramDividend_Classical_avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
import Theorems.Thm_AvramDividend_Classical_avram_gledger144_original_clipped_gaussian_physical_positive_integrable__v3
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
    (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω; let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          Real.exp (-(q * (s : ℝ))) *
            (deriv w y * z + (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0)
    let G : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * (X.generator w y - q * w y)
        else 0)
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤ ε := by
  let A : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    (Finset.sum (Finset.range (m + 1)) (fun i => (E (v (i + 1)) - E (v i)) * w (Y (v i)))) +
    Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0)
  let B : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (Finset.sum (Finset.range (m + 1)) (fun i => E (v (i + 1)) * (w (Z i) - w (Y (v i))))) -
    (Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := Y s
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        E s * (deriv w y * z + (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0)) -
    (Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0))
  refine avram_gledger143_measurable_residual_two_absolute_L1_errors_glue_positive
    P _ _ _ A B ?_ ?_ ?_ ?_
  · intro m ω
    exact avram_gledger142_original_physical_gaussian_source_exact_two_error_split__v2
      X q w x D n ρ m ω
  · intro m
    exact avram_gledger144_original_clipped_gaussian_physical_positive_integrable__v3
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  · exact avram_gledger139_original_clipped_postpayment_discount_euler_absolute_L1
      X hX q hq w C hC hTopCap hw_smooth x hx hxc
      D hD n hn τ hτeq ρ hρstop hρle j hprefix
  · exact avram_gledger140_original_clipped_postpayment_spatial_gaussian_Taylor_absolute_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix