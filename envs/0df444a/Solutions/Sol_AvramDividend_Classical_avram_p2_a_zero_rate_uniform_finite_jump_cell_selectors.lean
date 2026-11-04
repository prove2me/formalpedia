-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_finite_jump_cell_selectors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:13:53.494122+00:00
-- url     : https://prove2.me/submissions/86317de0-f66d-44a5-b64e-bbccb7aac9fb

import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_increment_to_jump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- Finitely many genuine positive-time original jumps admit one coherent
selector family of uniform mesh cells and their exact mark limits. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (F : Finset ℝ≥0)
    (hpos : ∀ t ∈ F, 0 < t)
    (hbound : ∀ t ∈ F, t ≤ T)
    (hL : ∀ t ∈ F,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t ∈ F, ContinuousWithinAt Y (Ici t) t) :
    ∃ idx : ℝ≥0 → ℕ → ℕ,
      (∀ t ∈ F, ∀ n, idx t n ≤ n ∧
        (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
        t ≤ (((idx t n + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1)))) ∧
      (∀ t ∈ F,
        Tendsto (fun n =>
          Y (((idx t n + 1 : ℕ) : ℝ≥0) *
            (T / ((n : ℝ≥0) + 1))) -
          Y ((idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
          atTop (𝓝 (Y t - Function.leftLim Y t))) := by
  classical
  have hall : ∀ t : ℝ≥0, ∃ i : ℕ → ℕ,
      (t ∈ F → ∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
        t ≤ (((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) ∧
      (t ∈ F → Tendsto (fun n =>
        Y (((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
        atTop (𝓝 (Y t - Function.leftLim Y t))) := by
    intro t
    by_cases ht : t ∈ F
    · obtain ⟨i, hcell, hmark⟩ :=
        avram_p2_a_zero_rate_uniform_cell_increment_to_jump
          Y T t hT (hpos t ht) (hbound t ht) (hL t ht) (hR t ht)
      exact ⟨i, fun _ => hcell, fun _ => hmark⟩
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · intro hmem
        exact (ht hmem).elim
      · intro hmem
        exact (ht hmem).elim
  let idx : ℝ≥0 → ℕ → ℕ := fun t => Classical.choose (hall t)
  refine ⟨idx, ?_, ?_⟩
  · intro t ht n
    exact (Classical.choose_spec (hall t)).1 ht n
  · intro t ht
    exact (Classical.choose_spec (hall t)).2 ht
