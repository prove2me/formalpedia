-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_true_finite_terminal_esscher_increment_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:13:45.226235+00:00
-- url     : https://prove2.me/submissions/b713923c-df34-434f-a88e-b4ef1ff4a198

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_mesh_path_vector_law_identification
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_grid_increment_vector_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (θ : ℝ) :
    Measure.map (fun v : Fin n → ℝ => fun i => v i.rev)
      (Measure.map
        (fun ω : Ω => fun i : Fin n =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((i.val : ℝ≥0) * δ) ω)
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))) =
    Measure.map
      (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))) := by
  let μ : Measure (Fin n → ℝ) :=
    (Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) P).withDensity
      (fun v : Fin n → ℝ => ENNReal.ofReal
        (Real.exp (θ * (∑ i : Fin n, v i) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))
  have hLaw := avram_ws01e_b_esscher_mesh_path_vector_law_identification
    X δ n θ
  have hR : Measurable (fun v : Fin n → ℝ => fun i : Fin n => v i.rev) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply i.rev
  change Measure.map (fun v : Fin n → ℝ => fun i : Fin n => v i.rev)
      (Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω)
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
            (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))) =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))))
  rw [hLaw]
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hR hA]
  exact avram_ws01e_b_esscher_grid_increment_vector_reversal
    X δ n θ A hA
