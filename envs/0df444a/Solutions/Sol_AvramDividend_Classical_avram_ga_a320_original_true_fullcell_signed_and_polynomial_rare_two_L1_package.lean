-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a320_original_true_fullcell_signed_and_polynomial_rare_two_L1_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:42:07.914656+00:00
-- url     : https://prove2.me/submissions/95450518-ed48-4a50-8a8f-24ad317b699b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a275_original_gaussian_true_physical_signed_exponential_tail_expected_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a277_original_gaussian_true_physical_signed_rare_exponential_tail_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : 0 < X.σ) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (θ δ : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ δ ≤ |R m i ω|
        then Real.exp (θ*R m i ω) else 0
    let Poly : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ δ ≤ |R m i ω|
        then 1+|R m i ω|+(Z m i ω)^2/2 else 0
    (∀ m, Integrable (Signed m) P) ∧
    (∀ m, Integrable (Poly m) P) ∧
    Tendsto (fun m => ∫ ω, Signed m ω ∂P) atTop (𝓝 (0:ℝ)) ∧
    Tendsto (fun m => ∫ ω, Poly m ω ∂P) atTop (𝓝 (0:ℝ)) := by
  intro Δ s R Z Signed Poly
  have hSI := avram_ga_a277_original_gaussian_true_physical_signed_rare_exponential_tail_integrable
    X hν hσ n ρ hρstop θ δ hθ
  have hSL := avram_ga_a275_original_gaussian_true_physical_signed_exponential_tail_expected_L1
    X hν hσ n hn ρ hρstop θ δ hθ hδ hSI
  have hPI := avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
    X hν n ρ hρstop δ hδ
  have hPL := avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
    X hν hσ n ρ hρstop δ hδ hPI
  exact ⟨hSI,hPI,hSL,hPL⟩
