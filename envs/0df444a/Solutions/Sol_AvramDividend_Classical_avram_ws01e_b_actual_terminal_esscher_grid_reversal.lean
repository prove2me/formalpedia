-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_terminal_esscher_grid_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T09:05:24.266793+00:00
-- url     : https://prove2.me/submissions/641b49f3-e308-46ef-a472-68bd6ec875b8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_esscher_weighted_path_increment_vector_reversal

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
      (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ A}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
        (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ)))
      {ω : Ω | (fun i : Fin n =>
        X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
        X.X ((i.val : ℝ≥0) * δ) ω) ∈ A}) := by
  have hSym := avram_ws01e_b_esscher_weighted_path_increment_vector_reversal
    X δ n θ A hA
  have hSum (ω : Ω) :
      (∑ i : Fin n,
        (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
         X.X ((i.val : ℝ≥0) * δ) ω)) =
      X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω :=
    avram_ws01e_b_fin_mesh_increment_sum_terminal X δ n ω
  have hWeight :
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (∑ i : Fin n,
          (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
            X.X ((i.val : ℝ≥0) * δ) ω)) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))) =
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * (X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω) -
          (((n : ℝ≥0) * δ : ℝ≥0) : ℝ) * X.ψ θ))) := by
    funext ω
    rw [hSum ω]
  simpa only [hWeight] using hSym
