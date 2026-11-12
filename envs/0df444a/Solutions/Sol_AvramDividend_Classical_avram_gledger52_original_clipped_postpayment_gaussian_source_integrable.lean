-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger52_original_clipped_postpayment_gaussian_source_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:26:23.401193+00:00
-- url     : https://prove2.me/submissions/87c77cad-dd91-40c0-b956-279e669e8f89

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger24_original_postpayment_raw_compact_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gledger53_original_clipped_physical_source_positive_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original stopped Gaussian residual has an integrable positive part
    whenever its physical source has an integrable positive part and its
    centred Gaussian grid is integrable on the same probability space. -/
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
    let M : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          Real.exp (-(q * (s : ℝ))) *
            (deriv w y * z +
              (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0)
    ∀ m : ℕ,
      Integrable (fun ω => max (S m ω - M m ω) (0 : ℝ)) P := by
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

  let M : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        Real.exp (-(q * (s : ℝ))) *
          (deriv w y * z +
            (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0)

  change ∀ m : ℕ,
    Integrable (fun ω => max (S m ω - M m ω) (0 : ℝ)) P
  intro m
  have hm : Integrable (M m) P :=
    (avram_gledger24_original_postpayment_raw_compact_grid_centered
      X hBV hNuZero q (le_of_lt hq) w C hTopCap hw_smooth
      x hx D hD.1.1 ρ hρstop j n m hprefix).1
  obtain ⟨hSmeas, hSpos⟩ :=
    avram_gledger53_original_clipped_physical_source_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  have hAmeas : AEStronglyMeasurable
      (fun ω => max (S m ω - M m ω) (0 : ℝ)) P := by
    exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
      (hSmeas.sub hm.aestronglyMeasurable)
  have hB : Integrable
      (fun ω => max (S m ω) (0 : ℝ) + |M m ω|) P :=
    hSpos.add hm.abs
  apply Integrable.mono' hB hAmeas
  filter_upwards [] with ω
  have hs : S m ω ≤ max (S m ω) (0 : ℝ) := le_max_left _ _
  have h0 : 0 ≤ max (S m ω) (0 : ℝ) := le_max_right _ _
  have hmneg : -(M m ω) ≤ |M m ω| := neg_le_abs _
  have hb : max (S m ω - M m ω) (0 : ℝ) ≤
      max (S m ω) (0 : ℝ) + |M m ω| := by
    apply max_le
    · linarith
    · linarith [abs_nonneg (M m ω)]
  have ha0 : 0 ≤ max (S m ω - M m ω) (0 : ℝ) := le_max_right _ _
  simp only [Real.norm_eq_abs, abs_of_nonneg ha0,
    abs_of_nonneg (add_nonneg h0 (abs_nonneg (M m ω)))]
  exact hb
