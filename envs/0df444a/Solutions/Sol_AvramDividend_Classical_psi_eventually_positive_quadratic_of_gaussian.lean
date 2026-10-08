-- Prove2me | solution 1 for AvramDividend.Classical.psi_eventually_positive_quadratic_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:50:05.787076+00:00
-- url     : https://prove2.me/submissions/52559ed9-9dfe-495c-8317-1db0e1b7dd31

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hσ : 0 < X.σ) :
    ∃ β C : ℝ, 0 ≤ β ∧ 0 ≤ C ∧
      ∀ θ : ℝ, β ≤ θ →
        q < X.ψ θ ∧ X.ψ θ - q ≤ C * (1 + θ ^ 2) := by
  obtain ⟨β0, hβ0, hψ⟩ :=
    psi_eventually_gt_of_gaussian X q hσ
  let C0 : ℝ := |X.c| + X.σ ^ 2 / 2 +
    ∫ y in Ioo (-1 : ℝ) 0, y ^ 2 ∂X.ν
  let β : ℝ := max 1 β0
  refine ⟨β, |C0| + |q|, ?_, ?_, ?_⟩
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 β0)
  · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro θ hθ
    have h1 : 1 ≤ θ := (le_max_left (1 : ℝ) β0).trans hθ
    have hψupper : X.ψ θ ≤ C0 * θ ^ 2 :=
      psi_quadratic_upper X θ h1
    have hca : 0 ≤ |C0| := abs_nonneg C0
    have hqa : 0 ≤ |q| := abs_nonneg q
    have hsq : 0 ≤ θ ^ 2 := sq_nonneg θ
    have hdif : 0 ≤ (|C0| - C0) * θ ^ 2 :=
      mul_nonneg (by linarith [le_abs_self C0]) hsq
    refine ⟨hψ θ ((le_max_right (1 : ℝ) β0).trans hθ), ?_⟩
    nlinarith [le_abs_self C0, neg_le_abs q]
