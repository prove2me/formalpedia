-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fin_mesh_increment_sum_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:57:50.695169+00:00
-- url     : https://prove2.me/submissions/ab482472-2a94-4be3-b11f-26af3db0299a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_equal_mesh_increment_sum_telescopes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n,
      (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
       X.X ((i.val : ℝ≥0) * δ) ω)) =
    X.X ((n : ℝ≥0) * δ) ω - X.X 0 ω := by
  calc
    (∑ i : Fin n,
      (X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
       X.X ((i.val : ℝ≥0) * δ) ω)) =
        Finset.sum (Finset.range n) (fun j : ℕ =>
          X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
          X.X ((j : ℝ≥0) * δ) ω) := by
            exact Fin.sum_univ_eq_sum_range
              (fun j : ℕ =>
                X.X (((j + 1 : ℕ) : ℝ≥0) * δ) ω -
                X.X ((j : ℝ≥0) * δ) ω) n
    _ = _ := avram_ws01e_b_equal_mesh_increment_sum_telescopes X δ n ω
