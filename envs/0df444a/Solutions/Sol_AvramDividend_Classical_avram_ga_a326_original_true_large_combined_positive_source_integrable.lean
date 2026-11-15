-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a326_original_true_large_combined_positive_source_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:31:18.76083+00:00
-- url     : https://prove2.me/submissions/12f75994-a043-4b46-9c22-11683eea423f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a323_original_large_rare_combined_fullcell_positive_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a320_original_true_fullcell_signed_and_polynomial_rare_two_L1_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
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
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (δ : ℝ) (hδ : 0 < δ) :
    let Large : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ δ ≤ |R i| then F i else 0
    ∀ δ : ℝ, 0 < δ → ∀ m,
      Integrable (fun ω => max (Large δ m ω) 0) P := by
  intro Large δ' hδ' m
  have hσ := avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
    X hNuZero hBV
  obtain ⟨θ, K, M, hθ, hK, hM, hbound⟩ :=
    avram_ga_a319_original_true_fullcell_rare_positive_two_source_all_mesh_bound
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  have h320 :=
    avram_ga_a320_original_true_fullcell_signed_and_polynomial_rare_two_L1_package
      X hNuZero hσ n hn ρ hρstop θ δ' hθ hδ'
  have hMeas :=
    avram_ga_a323_original_large_rare_combined_fullcell_positive_aestrongly_measurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix δ hδ
  let Sig : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      if (s < ρ ω ∧ s + Δ ≤ ρ ω) ∧ δ' ≤ |R|
      then Real.exp (θ * R) else 0
  let Poly : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      if (s < ρ ω ∧ s + Δ ≤ ρ ω) ∧ δ' ≤ |R|
      then 1 + |R| + Z ^ 2 / 2 else 0
  have hSInt : Integrable Sig P := by
    simpa only [Sig] using h320.1 m
  have hPInt : Integrable Poly P := by
    simpa only [Poly] using h320.2.1 m
  have hSpos : ∀ ω, 0 ≤ Sig ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    dsimp
    split_ifs <;> positivity
  have hPpos : ∀ ω, 0 ≤ Poly ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    dsimp
    split_ifs <;> positivity
  have hBound : ∀ᵐ ω ∂P,
      max (Large δ' m ω) 0 ≤
        (K * Real.exp (θ * (x + ((j : ℝ) + 1)))) * Sig ω +
          M * Poly ω := by
    simpa only [Sig, Poly, and_assoc] using hbound δ' hδ' m
  have hFMeas : AEStronglyMeasurable
      (fun ω => max (Large δ' m ω) 0) P := by
    simpa only [and_assoc] using hMeas δ' hδ' m
  exact avram_ga_a325_nonnegative_measurable_Gaussian_source_integrable_two_positive_tail_majorant
    P (fun ω => max (Large δ' m ω) 0) Sig Poly
    (K * Real.exp (θ * (x + ((j : ℝ) + 1)))) M
    (mul_nonneg hK (le_of_lt (Real.exp_pos _))) hM
    hFMeas hSInt hPInt (Filter.Eventually.of_forall (fun ω => le_max_right _ _))
    (Filter.Eventually.of_forall hSpos) (Filter.Eventually.of_forall hPpos) hBound
