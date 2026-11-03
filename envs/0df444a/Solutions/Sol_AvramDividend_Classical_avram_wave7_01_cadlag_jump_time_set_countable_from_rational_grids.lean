-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_cadlag_jump_time_set_countable_from_rational_grids
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:05:21.503083+00:00
-- url     : https://prove2.me/submissions/a4bca80b-7f89-4fee-b97c-8a0df5ad977d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every càdlàg path has at most countably many nonzero jump times. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hRight : ∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u)
    (hLeft : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    Set.Countable {u : ℝ≥0 |
      0 < u ∧ Y u - Function.leftLim Y u ≠ 0} := by
  let Tminus : ℕ → ℝ≥0 := fun k =>
    (⨅ n : ℕ,
      {Z : ℝ≥0 → ℝ |
        grid (pairs k).1 < grid n ∧
        Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal
  let Tplus : ℕ → ℝ≥0 := fun k =>
    (⨅ n : ℕ,
      {Z : ℝ≥0 → ℝ |
        grid (pairs k).1 < grid n ∧
        Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤)
        (fun v : ℝ≥0 => -Y v)).toNNReal
  have hCover :=
    avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
      Y hRight hLeft grid hdense pairs hpairs
  have hSubset :
      {u : ℝ≥0 | 0 < u ∧ Y u - Function.leftLim Y u ≠ 0} ⊆
        Set.range Tminus ∪ Set.range Tplus := by
    intro u hu
    obtain ⟨hPos, hJump⟩ := hu
    rcases hCover u hPos hJump with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, hk⟩
    · exact Or.inr ⟨k, hk⟩
  exact ((Set.countable_range Tminus).union
    (Set.countable_range Tplus)).mono hSubset
