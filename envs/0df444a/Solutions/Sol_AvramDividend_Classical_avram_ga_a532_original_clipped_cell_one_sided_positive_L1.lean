-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a532_original_clipped_cell_one_sided_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:42:51.100318+00:00
-- url     : https://prove2.me/submissions/c82f4630-a13c-4e01-881c-25f11277d99e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a536_source_spatial_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a537_original_Taylor_cell_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a538_original_generator_cell_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a539_original_spatial_cell_AEStronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a533_one_sided_three_source_integrability
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
    let W : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      if 0 < ρ ω then
        E (v (i + 1)) * (w (Z i) - w (Y (v i))) -
          (if s < ρ ω then
            E s * (deriv w (Y s) * z +
              (iteratedDeriv 2 w (Y s) / 2) *
                (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
          else 0) -
          (if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
      else 0
    ∀ m i : ℕ, i < m →
      AEStronglyMeasurable (W m i) P ∧
      Integrable (fun ω => max (W m i ω) (0 : ℝ)) P := by
  classical
  intro W m i hi
  let A : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      if 0 < ρ ω then E (v (i + 1)) * (w (Z i) - w (Y (v i))) else 0
  let B : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
      if 0 < ρ ω ∧ s < ρ ω then E s * (deriv w (Y s) * z +
        (iteratedDeriv 2 w (Y s) / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      else 0
  let G : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      if 0 < ρ ω ∧ s < ρ ω then
        (Δ : ℝ) * E s * X.generator w (Y s)
      else 0
  have hA := avram_ga_a536_source_spatial_positive_L1 X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m i hi
  have hB := avram_ga_a537_original_Taylor_cell_L1 X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m i hi
  have hG := avram_ga_a538_original_generator_cell_L1 X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m i hi
  have hW := avram_ga_a539_original_spatial_cell_AEStronglyMeasurable
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop ρ hρstop hρle j hprefix m i hi
  have hsplit (ω : Ω) : W m i ω = A m i ω - B m i ω - G m i ω := by
    dsimp [W, A, B, G]
    by_cases hr : 0 < ρ ω
    · by_cases hs : (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) < ρ ω
      · simp [hr, hs]
      · simp [hr, hs]
    · simp [hr]
  have hEq : (fun ω => max (W m i ω) (0 : ℝ)) =
      (fun ω => max (A m i ω - B m i ω - G m i ω) (0 : ℝ)) := by
    funext ω
    rw [hsplit ω]
  have hMeas : AEStronglyMeasurable
      (fun ω => max (A m i ω - B m i ω - G m i ω) (0 : ℝ)) P := by
    rw [← hEq]
    exact (hW.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  have hInt := avram_ga_a533_one_sided_three_source_integrability
    (P := P) (A m i) (B m i) (G m i) hA hB hG hMeas
  rw [← hEq] at hInt
  exact ⟨hW, hInt⟩
