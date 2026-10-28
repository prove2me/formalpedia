-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_esscher_grid_increment_vector_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:05:30.927839+00:00
-- url     : https://prove2.me/submissions/3d17d89c-5f06-45b6-bddb-6eead1c22664

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_reverse_preserves_sum
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_increment_vector_tilted_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
        (fun v : Fin n → ℝ => ENNReal.ofReal
          (Real.exp (θ * (∑ i : Fin n, v i) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
      {v : Fin n → ℝ | (fun i => v i.rev) ∈ A} =
    ((Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
        (fun v : Fin n → ℝ => ENNReal.ofReal
          (Real.exp (θ * (∑ i : Fin n, v i) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) A := by
  let w : (Fin n → ℝ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (Real.exp (θ * (∑ i : Fin n, v i) -
      (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))
  have hSum : Measurable (fun v : Fin n → ℝ => ∑ i : Fin n, v i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hwR : ∀ v : Fin n → ℝ, w (fun i => v i.rev) = w v := by
    intro v
    simp only [w, avram_ws01e_b_fin_reverse_preserves_sum]
  exact avram_ws01e_b_levy_increment_vector_tilted_reversal
    X δ n w hw hwR A hA
