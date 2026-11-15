-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a375p_probability_expected_Gaussian_energy_cross_discount_selected_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:40:57.146609+00:00
-- url     : https://prove2.me/submissions/1eb1a9b6-43d3-4677-8c74-77d04b320fb0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
import Theorems.Thm_AvramDividend_Classical_avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (S : ℝ → ℕ → Ω → ℝ) (E C : ℕ → Ω → ℝ)
    (n : ℕ) (q L M K : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hSm : ∀ δ, 0 < δ → ∀ m,
      AEStronglyMeasurable (fun ω => max (S δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hCI : ∀ m, Integrable (C m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hCL : Tendsto (fun m => ∫ ω, C m ω ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ m, ∀ᵐ ω ∂P,
        max (S δ m ω) 0 ≤
          ε*E m ω+(M/2)*C m ω +
          (m : ℝ) *
            (q * (((n : ℝ≥0) / ((m : ℝ≥0)+1) : ℝ≥0) : ℝ) * L)^2 /
              (2*ε)) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧
      (∀ m, Integrable (fun ω => max (S δ m ω) 0) P) ∧
      ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (S δ m ω) 0 ∂P) ≤ η := by
  classical
  let A : ℕ → Ω → ℝ := fun m ω => (M/2) * C m ω
  let B : ℝ → ℕ → Ω → ℝ := fun ε m _ =>
    (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 *
      ((m : ℝ) * (1/(2*ε)))
  have hAI : ∀ m, Integrable (A m) P := by
    intro m
    exact (hCI m).const_mul (M/2)
  have hBI : ∀ ε, 0 < ε → ∀ m, Integrable (B ε m) P := by
    intro ε hε m
    exact integrable_const _
  have hConst : Tendsto (fun _ : ℕ => M/2) atTop (𝓝 (M/2)) :=
    tendsto_const_nhds
  have hAL : Tendsto (fun m => ∫ ω, A m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    simpa [A, integral_const_mul] using hConst.mul hCL
  have hBL : ∀ ε, 0 < ε →
      Tendsto (fun m => ∫ ω, B ε m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
    intro ε hε
    have ht := avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
      n q L (1/(2*ε))
    simpa [B] using ht
  have hMod' : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ m, ∀ᵐ ω ∂P,
        max (S δ m ω) 0 ≤ ε * E m ω + A m ω + B ε m ω := by
    intro ε hε
    obtain ⟨δ,hδ,hh⟩ := hMod ε hε
    refine ⟨δ,hδ,?_⟩
    intro m
    filter_upwards [hh m] with ω hω
    have hEq : (m : ℝ) *
        (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 / (2*ε) =
        (q * (((n : ℝ≥0) / ((m : ℝ≥0) + 1) : ℝ≥0) : ℝ) * L)^2 *
          ((m : ℝ) * (1/(2*ε))) := by
      ring
    rw [hEq] at hω
    simpa only [A,B] using hω
  exact avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
    P S E A B K hK hSm hEI hAI hBI hEB hAL hBL hMod'
