-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger140_original_clipped_postpayment_spatial_gaussian_Taylor_absolute_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:12:26.588456+00:00
-- url     : https://prove2.me/submissions/f36cd5fa-6928-4c8f-8d47-9a86f9544e3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger178_original_clipped_postpayment_spatial_gaussian_Taylor_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a26_original_stopped_gaussian_signed_residual_mean
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
      Integrable (fun ω => |B m ω|) P ∧
      (∫ ω, |B m ω| ∂P) ≤ ε := by
  intro B ε hε
  obtain ⟨kp, hp⟩ :=
    avram_gledger178_original_clipped_postpayment_spatial_gaussian_Taylor_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix (ε / 4) (by positivity)
  obtain ⟨ks, hs⟩ :=
    avram_ga_a26_original_stopped_gaussian_signed_residual_mean
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix (ε / 2) (by positivity)
  refine ⟨max kp ks, ?_⟩
  intro m hm
  obtain ⟨hpI, hpε⟩ := hp m (le_trans (le_max_left kp ks) hm)
  obtain ⟨hsI, hsε⟩ := hs m (le_trans (le_max_right kp ks) hm)
  have habs (u : ℝ) : |u| = 2 * max u 0 - u := by
    rcases le_total u 0 with hu | hu
    · rw [abs_of_nonpos hu, max_eq_right hu]
      ring
    · rw [abs_of_nonneg hu, max_eq_left hu]
      ring
  have hId : (fun ω => |B m ω|) =
      (fun ω => (2 : ℝ) * max (B m ω) 0 - B m ω) := by
    funext ω
    exact habs (B m ω)
  have hIabs : Integrable (fun ω => |B m ω|) P := by
    rw [hId]
    exact (hpI.const_mul 2).sub hsI
  refine ⟨hIabs, ?_⟩
  calc
    (∫ ω, |B m ω| ∂P) =
        (∫ ω, (2 : ℝ) * max (B m ω) 0 ∂P) -
        ∫ ω, B m ω ∂P := by
      rw [hId]
      exact integral_sub (hpI.const_mul 2) hsI
    _ = 2 * (∫ ω, max (B m ω) 0 ∂P) -
        ∫ ω, B m ω ∂P := by
      rw [integral_const_mul]
    _ ≤ ε := by
      have hslower := (abs_le.mp hsε).1
      linarith
