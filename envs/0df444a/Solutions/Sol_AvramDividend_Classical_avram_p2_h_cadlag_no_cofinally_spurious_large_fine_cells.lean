-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_no_cofinally_spurious_large_fine_cells
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:21:31.72575+00:00
-- url     : https://prove2.me/submissions/1fc6ddb6-ee3d-46a0-a0a3-d2f5eaae4311

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal

/-- There cannot be cofinally many arbitrarily fine large cells that
avoid every actual jump of the same magnitude in their right-closed cell. -/
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
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t)
    (hbad : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ i : ℕ, ρ ≤ |Y (b n i) - Y (a n i)| ∧
        ∀ t : ℝ≥0, ¬
          (a n i < t ∧ t ≤ b n i ∧
            ρ ≤ |Y t - Function.leftLim Y t|)) :
    False := by
  classical
  let ns : ℕ → ℕ := fun k => Classical.choose (hbad k)
  let is : ℕ → ℕ := fun k =>
    Classical.choose ((Classical.choose_spec (hbad k)).2)
  have hng : ∀ k, k ≤ ns k := by
    intro k
    exact (Classical.choose_spec (hbad k)).1
  have hns : Tendsto ns atTop (atTop : Filter ℕ) := by
    apply Filter.tendsto_atTop.2
    intro j
    exact Filter.eventually_atTop.2
      ⟨j, fun k hk => le_trans hk (hng k)⟩
  let A : ℕ → ℝ≥0 := fun k => a (ns k) (is k)
  let B : ℕ → ℝ≥0 := fun k => b (ns k) (is k)
  have hcell : ∀ k, ρ ≤ |Y (B k) - Y (A k)| ∧
      ∀ t : ℝ≥0, ¬ (A k < t ∧ t ≤ B k ∧
        ρ ≤ |Y t - Function.leftLim Y t|) := by
    intro k
    exact Classical.choose_spec ((Classical.choose_spec (hbad k)).2)
  have hgap : Tendsto (fun k => (B k : ℝ) - (A k : ℝ))
      atTop (𝓝 (0 : ℝ)) := hwidth is ns hns
  obtain ⟨t, ht, ψ, _, hcross, hjump⟩ :=
    avram_p2_h_cadlag_compact_large_cells_have_actual_jump_inside_subsequence
      Y T A B ρ hρ
      (fun k => hab (ns k) (is k))
      (fun k => hbound (ns k) (is k))
      hgap (fun k => (hcell k).1) hL hR
  exact ((hcell (ψ 0)).2 t) ⟨(hcross 0).1, (hcross 0).2, hjump⟩
