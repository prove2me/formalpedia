-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_esscher_weighted_path_increment_grid_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:22:47.152766+00:00
-- url     : https://prove2.me/submissions/744dd607-889c-453c-bfd6-0daa8d81d7db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_map_withDensity_observable_density
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset Set
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) -
         (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {ω : Ω | (fun i : Fin n =>
          X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A} =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) -
         (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {ω : Ω | (fun i : Fin n =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((i.val : ℝ≥0) * δ) ω) ∈ A} := by
  let F : Ω → (Fin n → ℝ) := fun ω i =>
    X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
    X.X ((i.val : ℝ≥0) * δ) ω
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (θ * (∑ i : Fin n, v i) -
      (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    exact (X.adapted.measurable).sub (X.adapted.measurable)
  have hw : Measurable w := by
    have hsum : Measurable (fun v : Fin n → ℝ => ∑ i : Fin n, v i) :=
      Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
    dsimp [w]
    fun_prop
  have hR : MeasurableSet {v : Fin n → ℝ | (fun i => v i.rev) ∈ A} := by
    exact hA.preimage (by fun_prop)
  have hPush := avram_ws01e_b_map_withDensity_observable_density P F hF w hw
  have hRev := avram_ws01e_b_esscher_grid_increment_vector_reversal
    X δ n θ A hA
  change (P.withDensity (w ∘ F)) (F ⁻¹' {v | (fun i => v i.rev) ∈ A}) =
    (P.withDensity (w ∘ F)) (F ⁻¹' A)
  rw [← Measure.map_apply hF hR, ← Measure.map_apply hF hA]
  rw [hPush]
  exact hRev
