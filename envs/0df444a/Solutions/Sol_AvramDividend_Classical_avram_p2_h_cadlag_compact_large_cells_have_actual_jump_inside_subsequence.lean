-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:10:59.720529+00:00
-- url     : https://prove2.me/submissions/7d1f7f0b-5d64-4eb0-b3a4-35421afb83c6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Persistently large fine compact-horizon increments have a cofinal
subsequence of actual jump-containing cells. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (a b : ℕ → ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (hab : ∀ n, a n ≤ b n)
    (hbound : ∀ n, b n ≤ T)
    (hgap : Tendsto (fun n => (b n : ℝ) - (a n : ℝ))
      atTop (𝓝 (0 : ℝ)))
    (hlarge : ∀ n, ρ ≤ |Y (b n) - Y (a n)|)
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∃ t : ℝ≥0, t ≤ T ∧
      ∃ ψ : ℕ → ℕ,
        Tendsto ψ atTop (atTop : Filter ℕ) ∧
        (∀ n, a (ψ n) < t ∧ t ≤ b (ψ n)) ∧
        ρ ≤ |Y t - Function.leftLim Y t| := by
  obtain ⟨t, ht, φ, hφ, hbφ⟩ :=
    avram_p2_h_cadlag_bounded_endpoint_has_convergent_subsequence T b hbound
  have hgapφ : Tendsto
      (fun n : ℕ => (b (φ n) : ℝ) - (a (φ n) : ℝ))
      atTop (𝓝 (0 : ℝ)) := hgap.comp hφ.tendsto_atTop
  have haφ : Tendsto (a ∘ φ) atTop (𝓝 t) :=
    avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
      (a ∘ φ) (b ∘ φ) t hbφ hgapφ
  obtain ⟨η, hη, hcross, hactual⟩ :=
    avram_p2_h_cadlag_large_shrinking_cells_have_crossing_subsequence
      Y t (a ∘ φ) (b ∘ φ)
      (fun n => hab (φ n)) haφ hbφ (hL t ht) (hR t ht)
      ρ hρ (fun n => hlarge (φ n))
  refine ⟨t, ht, φ ∘ η, hφ.tendsto_atTop.comp hη, ?_, hactual⟩
  intro n
  exact hcross n
