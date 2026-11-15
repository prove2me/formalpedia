-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a313_original_true_fullcell_rare_polynomial_expected_L1_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:35:33.915207+00:00
-- url     : https://prove2.me/submissions/71ef4e83-ab6d-43db-9d58-7b95fd5508a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (δ : ℝ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let Poly : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
           δ ≤ |R m i ω| then
          1 + |R m i ω| + (Z m i ω)^2 / 2 else 0
    (∀ m, Integrable (Poly m) P) ∧
      Tendsto (fun m => ∫ ω, Poly m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  have hI := avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
    X hν n ρ hρstop δ hδ
  have hL := avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
    X hν hσ n ρ hρstop δ hδ hI
  exact ⟨hI,hL⟩
