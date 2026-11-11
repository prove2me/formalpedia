-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger28_original_clipped_source_vs_postpayment_gaussian_mesh
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:26:15.444942+00:00
-- url     : https://prove2.me/submissions/c3540080-031e-40d0-94e3-02d06d918c30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger50_original_clipped_gaussian_physical_Taylor_L1
import Theorems.Thm_AvramDividend_Classical_avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_gledger52_original_clipped_postpayment_gaussian_source_integrable
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
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω) (0 : ℝ) ∂P) ≤ ε := by
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
  let G : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then
        let y := x + X.X s ω - rightLimit D s ω
        (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
          (X.generator w y - q * w y)
      else 0)
  change ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
    Integrable (fun ω => max (S m ω - M m ω) (0 : ℝ)) P ∧
    (∫ ω, max (S m ω - M m ω) (0 : ℝ) ∂P) ≤ ε
  intro ε hε
  obtain ⟨k, hk⟩ :=
    avram_gledger50_original_clipped_gaussian_physical_Taylor_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix ε hε
  have hlow : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω := by
    filter_upwards [hprefix] with ω hω t ht hs
    exact (hω t ht hs).1
  refine ⟨k, ?_⟩
  intro m hm
  obtain ⟨hEint, hEbound⟩ := hk m hm
  have hAint : Integrable
      (fun ω => max (S m ω - M m ω) (0 : ℝ)) P :=
    avram_gledger52_original_clipped_postpayment_gaussian_source_integrable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  have hG : ∀ᵐ ω ∂P, G m ω ≤ 0 :=
    avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
      X q w C hTopCap (fun y hy hc => (hw_gen y hy hc).2)
      x D hD.1.1 ρ j n m hlow
  refine ⟨hAint, ?_⟩
  calc
    (∫ ω, max (S m ω - M m ω) (0 : ℝ) ∂P) ≤
        (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) := by
      apply integral_mono_ae hAint hEint
      filter_upwards [hG] with ω hg
      apply max_le
      · have h : S m ω - M m ω ≤
          S m ω - M m ω - G m ω := by linarith
        exact h.trans (le_max_left _ _)
      · exact le_max_right _ _
    _ ≤ ε := hEbound
