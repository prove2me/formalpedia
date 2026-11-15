-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a361_original_small_fullcell_selected_threshold_integrable_positive_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:39:23.308999+00:00
-- url     : https://prove2.me/submissions/c8db3f79-3537-46aa-9ea5-b0ba89760cbe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a367_original_fullcell_raw_Gaussian_integrable_uniform_expected_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a342_original_small_fullcell_combined_positive_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a373_original_fullcell_small_ae_Young_rawenergy_cross_discount_modulus
import Theorems.Thm_AvramDividend_Classical_avram_ga_a375p_probability_expected_Gaussian_energy_cross_discount_selected_budget
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
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
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ |R i| < δ then F i else 0
    ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧
        (∀ m, Integrable (fun ω => max (Small δ m ω) 0) P) ∧
        ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
          (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro Small
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω => R m i ω - (Δ m : ℝ) * X.c
  let Energy : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
      then (R m i ω)^2 else 0
  let Cross : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
      then |(R m i ω)^2 - (Z m i ω)^2| else 0
  let K : ℝ := 2*((n : ℝ)*X.σ^2+((n : ℝ)*X.c)^2)
  have hEnergy := avram_ga_a367_original_fullcell_raw_Gaussian_integrable_uniform_expected_energy_package
    X hNuZero n ρ hρstop
  change 0 ≤ K ∧ (∀ m, Integrable (Energy m) P) ∧
    (∀ m, (∫ ω, Energy m ω ∂P) ≤ K) at hEnergy
  obtain ⟨hK,hEI,hEB⟩ := hEnergy
  have hCross := avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
    X hNuZero n ρ hρstop
  change (∀ m, Integrable (Cross m) P) ∧
    Tendsto (fun m => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) at hCross
  have hSm :=
    avram_ga_a342_original_small_fullcell_combined_positive_aestrongly_measurable
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix 1 (by norm_num)
  change ∀ δ, 0 < δ → ∀ m,
    AEStronglyMeasurable (fun ω => max (Small δ m ω) 0) P at hSm
  obtain ⟨L,M,hL,hM,hMod⟩ :=
    avram_ga_a373_original_fullcell_small_ae_Young_rawenergy_cross_discount_modulus
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix
  change ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
    ∀ m, ∀ᵐ ω ∂P, max (Small δ m ω) 0 ≤
      ε*Energy m ω+(M/2)*Cross m ω+
        (m : ℝ)*(q*((Δ m : ℝ≥0) : ℝ)*L)^2/(2*ε) at hMod
  exact avram_ga_a375p_probability_expected_Gaussian_energy_cross_discount_selected_budget
    (P := P) Small Energy Cross n q L M K hK hM hSm hEI hCross.1 hEB
    hCross.2 hMod
