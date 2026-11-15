-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:03:34.622215+00:00
-- url     : https://prove2.me/submissions/f0ffb9cc-9a1f-4762-865a-45ee0fe8cc0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
import Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
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
    (hσ : 0 < X.σ) (n : ℕ) (ρ : Ω → ℝ≥0)
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
    (∀ m, Integrable (Poly m) P) →
      Tendsto (fun m => ∫ ω, Poly m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro Δ s R Z Poly hPI
  let Square : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω then
        (if δ ≤ |R m i ω| then (R m i ω)^2 else 0) else 0
  have hQI : ∀ m, Integrable (Square m) P := by
    simpa only [Square,R,s,Δ] using
      (avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
        X hν n ρ hρstop δ)
  have hQLim : Tendsto (fun m => ∫ ω, Square m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Square,R,s,Δ] using
      (avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
        X hν hσ n ρ hρstop δ hδ)
  let C : ℝ := 1/δ^2 + 1/δ + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hPt := avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
    X n ρ δ hδ
  change ∀ᶠ m : ℕ in atTop, ∀ ω : Ω, Poly m ω ≤ C * Square m ω at hPt
  have hUpper : ∀ᶠ m : ℕ in atTop,
      (∫ ω, Poly m ω ∂P) ≤ C * (∫ ω, Square m ω ∂P) := by
    filter_upwards [hPt] with m hm
    calc
      (∫ ω, Poly m ω ∂P) ≤ ∫ ω, C * Square m ω ∂P :=
        integral_mono (hPI m) ((hQI m).const_mul C) hm
      _ = C * (∫ ω, Square m ω ∂P) := by rw [integral_const_mul]
  have hLow (m : ℕ) : 0 ≤ (∫ ω, Poly m ω ∂P) := by
    apply integral_nonneg
    intro ω
    dsimp [Poly]; apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have ht : Tendsto (fun m => C * (∫ ω, Square m ω ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hQLim.const_mul C
  exact squeeze_zero' (Filter.Eventually.of_forall hLow) hUpper ht
