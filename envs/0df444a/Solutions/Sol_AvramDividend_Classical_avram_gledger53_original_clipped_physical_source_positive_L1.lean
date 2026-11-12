-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger53_original_clipped_physical_source_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:17:13.554271+00:00
-- url     : https://prove2.me/submissions/3b65c060-0dcd-4f0c-a7ee-ab9aba0d8567

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger66_original_clipped_finite_source_positive_integrable_of_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gledger68_original_clipped_source_observable_envelope_package
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The remaining physical source package implies exactly the original
    clipped stopped Gaussian positive-part L1, with one-sided integration
    supplied by the already-Proved gledger66. -/
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
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let S : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    ∀ m : ℕ, AEStronglyMeasurable (S m) P ∧
      Integrable (fun ω => max (S m ω) (0 : ℝ)) P := by
  intro S m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  obtain ⟨hFinite, θ, K, b, hK, hb, hSmeas, hE0, hE1, hcell, hexp⟩ :=
    avram_gledger68_original_clipped_source_observable_envelope_package
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  letI : IsFiniteMeasure P := hFinite
  have hInt : Integrable (fun ω => max
      (Finset.sum (Finset.range (m + 1)) (fun i =>
        (E (i + 1) ω - E i ω) * w (Y i ω) +
        E (i + 1) ω * (w (Z i ω) - w (Y i ω)))) 0) P :=
    avram_gledger66_original_clipped_finite_source_positive_integrable_of_envelope
      m E Y Z w θ K b hK hb hSmeas.aemeasurable
      hE0 hE1 hcell hexp
  exact ⟨hSmeas, hInt⟩
