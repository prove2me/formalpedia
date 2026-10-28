-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fin_mesh_increment_sum_eq_terminal_displacement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:34:56.695764+00:00
-- url     : https://prove2.me/submissions/12121a54-9fa7-420f-af78-f6b514759aee

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fin_mesh_increment_sum_terminal

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
  exact avram_ws01e_b_fin_mesh_increment_sum_terminal X δ n ω
