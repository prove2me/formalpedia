-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a216_original_combined_fullcell_one_sided_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:17:47.069435+00:00
-- url     : https://prove2.me/submissions/2cf456de-b3cd-4a78-9301-35ab4c162ca3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a360_positive_partition_glue_with_selected_threshold_integrability
import Theorems.Thm_AvramDividend_Classical_avram_ga_a361_original_small_fullcell_selected_threshold_integrable_positive_budget
import Theorems.Thm_AvramDividend_Classical_avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a266_full_physical_source_positive_small_large_raw_partition
import Theorems.Thm_AvramDividend_Classical_avram_ga_a267_original_combined_fullcell_positive_aestrongly_measurable
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
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Full : ℕ → Ω → ℝ := fun m ω =>
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
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    (∀ m, Integrable (fun ω => max (Full m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Full m ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  intro Full
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω
  let Cell : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℝ := R m i ω - (Δ m : ℝ) * X.c
    E (s m i + Δ m) * (w (Y (s m i) + R m i ω) - w (Y (s m i))) -
      E (s m i) * (deriv w (Y (s m i)) * R m i ω +
        iteratedDeriv 2 w (Y (s m i)) / 2 * Z^2)
  let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω ∧ |R m i ω| < δ
      then Cell m i ω else 0
  let Large : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω ∧ δ ≤ |R m i ω|
      then Cell m i ω else 0
  have hMeas := avram_ga_a267_original_combined_fullcell_positive_aestrongly_measurable
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix
  have hSmall := avram_ga_a361_original_small_fullcell_selected_threshold_integrable_positive_budget
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix
  have hLarge := fun δ (hδ : 0 < δ) =>
    avram_ga_a263_original_combined_fullcell_large_raw_increment_positive_L1
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix δ hδ
  change (∀ m, AEStronglyMeasurable (fun ω => max (Full m ω) 0) P) at hMeas
  change ∀ η, 0 < η → ∃ δ, 0 < δ ∧
    (∀ m, Integrable (fun ω => max (Small δ m ω) 0) P) ∧
    ∃ k : ℕ, ∀ m, k ≤ m →
      (∫ ω, max (Small δ m ω) 0 ∂P) ≤ η at hSmall
  have hFullEq (m : ℕ) (ω : Ω) :
      Full m ω =
        ∑ i ∈ Finset.range m,
          if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
          then Cell m i ω else 0 := by
    rfl
  have hPart (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (ω : Ω) :
      max (Full m ω) 0 ≤
        max (Small δ m ω) 0 + max (Large δ m ω) 0 := by
    have h := avram_ga_a266_full_physical_source_positive_small_large_raw_partition
      (Finset.range m)
      (fun i ω => s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω)
      (fun i ω => R m i ω)
      (fun i ω => Cell m i ω) δ ω
    rw [hFullEq m ω]
    simpa only [Small, Large, and_assoc] using h
  exact avram_ga_a360_positive_partition_glue_with_selected_threshold_integrability
    P Full Small Large hMeas (fun δ hδ => (hLarge δ hδ).1)
      hPart (fun δ hδ => (hLarge δ hδ).2) hSmall
