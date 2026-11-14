-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a222_raw_positive_Gaussian_exponential_tail_dominated_by_centered_normalised
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T01:00:59.558439+00:00
-- url     : https://prove2.me/submissions/b596d61f-fd1c-4f4c-8e19-4f5162fa1a59

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a200_raw_positive_large_cell_to_centered_gaussian_chernoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (θ δ σ d r : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hσ : 0 < σ) (hd : |d| ≤ δ / 2) :
    (if δ ≤ r then Real.exp (θ * r) else 0) ≤
      Real.exp (θ * |d|) *
        (if δ / (2 * σ) ≤ (r - d) / σ
        then Real.exp ((θ * σ) * ((r - d) / σ)) else 0) := by
  classical
  by_cases hr : δ ≤ r
  · obtain ⟨hcut,hbound⟩ :=
      avram_ga_a200_raw_positive_large_cell_to_centered_gaussian_chernoff
        θ δ σ d r hθ hδ hσ hd hr
    simpa only [if_pos hr, if_pos hcut] using hbound
  · simp only [if_neg hr]
    by_cases hc : δ / (2 * σ) ≤ (r - d) / σ
    · simp only [if_pos hc]
      positivity
    · simp only [if_neg hc, mul_zero, le_refl]
