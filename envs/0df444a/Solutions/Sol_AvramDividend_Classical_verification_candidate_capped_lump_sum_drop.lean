-- Prove2me | solution 1 for AvramDividend.Classical.verification_candidate_capped_lump_sum_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:53:51.987039+00:00
-- url     : https://prove2.me/submissions/62298079-e698-4472-9df6-03b5d69d220b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_verification_candidate_lump_sum_drop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
open AvramDividend.Classical

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_diff : DifferentiableOn ℝ w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u δ : ℝ) (hδ : 0 ≤ δ) (hpost : 0 ≤ u - δ)
    (hcap : ENNReal.ofReal u ≤ C) :
    δ ≤ w u - w (u - δ) := by
  have hu0 : 0 ≤ u := by
    linarith
  have hcont : ContinuousOn w (Icc (u - δ) u) := by
    apply hw_cont.mono
    intro y hy
    exact le_trans hpost hy.1
  have hdomain :
      Ioo (u - δ) u ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have hy0 : 0 < y := lt_of_le_of_lt hpost hy.1
    have hy_nonneg : 0 ≤ y := le_of_lt hy0
    have hyu : ENNReal.ofReal y < ENNReal.ofReal u :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy_nonneg).2 hy.2
    exact ⟨hy0, lt_of_lt_of_le hyu hcap⟩
  have hdiff : DifferentiableOn ℝ w (Ioo (u - δ) u) :=
    hw_diff.mono hdomain
  have hgrad : ∀ y ∈ Ioo (u - δ) u, 1 ≤ deriv w y := by
    intro y hy
    have h := hdomain hy
    exact hw_grad y h.1 h.2
  exact verification_candidate_lump_sum_drop
    w u δ hδ hcont hdiff hgrad
