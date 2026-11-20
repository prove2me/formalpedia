-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_B_original_finitecap_grid_discounted_kink_localtime_sum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:38:19.358431+00:00
-- url     : https://prove2.me/submissions/3b5ae2c6-c3e4-42c9-8b45-579752ccb050

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (S : Finset ℕ) (j : ℕ → ℕ)
    (L E : ℕ → ℝ)
    (hL : ∀ i ∈ S, 0 ≤ L i)
    (hE : ∀ i ∈ S, 0 ≤ E i) :    let b : ℕ → ℝ := fun i =>
      C.toReal * ((((j i + 1 : ℕ) : ℝ) / ((j i + 2 : ℕ) : ℝ)))
    (∑ i ∈ S, E i * (((1 - deriv w (b i)) / 2) * L i)) ≤ 0 := by
  intro b
  apply Finset.sum_nonpos
  intro i hi
  simpa only [b] using
    (avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
      w C hC hFiniteCap hw_smooth hw_grad
      (j i) (L i) (E i) (hL i hi) (hE i hi))
