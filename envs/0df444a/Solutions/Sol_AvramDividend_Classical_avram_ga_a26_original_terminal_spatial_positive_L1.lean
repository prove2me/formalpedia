-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_original_terminal_spatial_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:06:33.90786+00:00
-- url     : https://prove2.me/submissions/322ec54e-79f2-4312-96a3-281624a4c46c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_dominated_zero_integral_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_terminal_positive_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_terminal_positive_ae_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Use the original stopping-time envelope and pointwise continuity for the last clipped cell. -/
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
    let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0) P ∧
      (∫ ω, (if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0) ∂P) ≤ ε := by
  intro Last
  let F : ℕ → Ω → ℝ := fun m ω =>
    if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
  obtain ⟨g, hg, hMeas, hDom⟩ :=
    avram_ga_a26_terminal_positive_envelope
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  have hLim : ∀ᵐ ω ∂P, Tendsto (fun m => F m ω) atTop (nhds (0 : ℝ)) :=
    avram_ga_a26_terminal_positive_ae_zero
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix
  have hRes :=
    avram_ga_a26_dominated_zero_integral_epsilon
      P F g hMeas hg hDom hLim
  simpa only [F] using hRes
