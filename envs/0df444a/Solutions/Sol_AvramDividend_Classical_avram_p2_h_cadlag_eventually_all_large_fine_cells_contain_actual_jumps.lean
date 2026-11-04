-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_eventually_all_large_fine_cells_contain_actual_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:40:29.054885+00:00
-- url     : https://prove2.me/submissions/0785a48e-5fb8-4f8a-9e95-5b70214a352f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Uniform exclusion of spurious large jumps on any indexed
family whose cell widths shrink along all cofinal level selectors. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℕ → ℕ → ℝ≥0)
    (hab : ∀ n i, a n i ≤ b n i)
    (hbound : ∀ n i, b n i ≤ T)
    (hwidth : ∀ (is ns : ℕ → ℕ),
      Tendsto ns atTop (atTop : Filter ℕ) →
      Tendsto (fun k => (b (ns k) (is k) : ℝ) -
        (a (ns k) (is k) : ℝ)) atTop (𝓝 (0 : ℝ)))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i : ℕ,
      ρ ≤ |Y (b n i) - Y (a n i)| →
        ∃ t : ℝ≥0, a n i < t ∧ t ≤ b n i ∧
          ρ ≤ |Y t - Function.leftLim Y t| := by
  classical
  by_contra h
  push_neg at h
  apply avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells
    Y T ρ hρ a b hab hbound hwidth hL hR
  intro N
  obtain ⟨n, hn, i, hi, hsmall⟩ := h N
  refine ⟨n, hn, i, hi, ?_⟩
  intro t ht
  exact (not_le_of_gt (hsmall t ht.1 ht.2.1)) ht.2.2
