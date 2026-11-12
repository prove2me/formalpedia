-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger178_original_clipped_postpayment_spatial_gaussian_Taylor_positive_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:24:09.466213+00:00
-- url     : https://prove2.me/submissions/4fcc2401-ca82-42e5-b04b-90446b699027
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger176_original_gaussian_spatial_zero_clock_exact
import Theorems.Thm_AvramDividend_Classical_avram_gledger179_original_clipped_gaussian_spatial_positive_clock_L1
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
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      (∑ i ∈ Finset.range (m + 1),
        E (v (i + 1)) * (w (Z i) - w (Y (v i)))) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := Y s
          let z := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
          E s * (deriv w y * z +
            (iteratedDeriv 2 w y / 2) * (z ^ 2 - (Δ : ℝ) * X.σ ^ 2))
        else 0) -
      (∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then (Δ : ℝ) * E s * X.generator w (Y s) else 0)
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (B m ω) (0 : ℝ)) P ∧
      (∫ ω, max (B m ω) (0 : ℝ) ∂P) ≤ ε := by
  intro B ε hε
  obtain ⟨k, hk⟩ :=
    avram_gledger179_original_clipped_gaussian_spatial_positive_clock_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix ε hε
  refine ⟨k, ?_⟩
  intro m hm
  have hBzero (ω : Ω) (hclock : ρ ω = 0) : B m ω = 0 := by
    exact avram_gledger176_original_gaussian_spatial_zero_clock_exact
      X x D w q ρ ω hclock n m
  have hEq : (fun ω => if 0 < ρ ω then max (B m ω) (0 : ℝ) else 0) =
      (fun ω => max (B m ω) (0 : ℝ)) := by
    funext ω
    by_cases hclock : 0 < ρ ω
    · simp [hclock]
    · have hρzero : ρ ω = 0 := by
        apply le_antisymm (le_of_not_gt hclock)
        positivity
      simp [hclock, hBzero ω hρzero]
  have hresult := hk m hm
  simpa only [← hEq] using hresult
