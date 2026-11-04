-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:07:55.859071+00:00
-- url     : https://prove2.me/submissions/b5ed7cf8-7bdf-417c-89a2-4543a0c1b689

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_all_negative_jump_mesh_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Source-path uniform negative-cell counts dominate the number of actual
negative jumps, even when the path has infinitely many small jumps. -/
theorem solution (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε) :
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      ((((Finset.range (n + 1)).image
        (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
        (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞))
      atTop := by
  classical
  letI : DecidableEq ℝ≥0 := fun a b => Classical.propDecidable (a = b)
  let d : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 1)
  have hcell (u : ℝ≥0) (hu : u ∈ S) : ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧ (i n : ℝ≥0) * d n < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * d n) ∧
      Tendsto (fun n => (i n : ℝ≥0) * d n) atTop (𝓝[<] u) ∧
      Tendsto (fun n => ((i n + 1 : ℕ) : ℝ≥0) * d n)
        atTop (nhdsWithin u (Ici u)) := by
    exact avram_p2_34dbea70_uniform_source_jump_cells_sided_limits
      T u hT (hTimes u hu).1 (hTimes u hu).2
  let idx (u : ℝ≥0) : ℕ → ℕ :=
    if hu : u ∈ S then Classical.choose (hcell u hu) else fun _ => 0
  have hspec (u : ℝ≥0) (hu : u ∈ S) :
      (∀ n, idx u n ≤ n ∧ (idx u n : ℝ≥0) * d n < u ∧
        u ≤ ((idx u n + 1 : ℕ) : ℝ≥0) * d n) ∧
      Tendsto (fun n => (idx u n : ℝ≥0) * d n) atTop (𝓝[<] u) ∧
      Tendsto (fun n => ((idx u n + 1 : ℕ) : ℝ≥0) * d n)
        atTop (nhdsWithin u (Ici u)) := by
    simpa only [idx, dif_pos hu] using Classical.choose_spec (hcell u hu)
  let a : ℝ≥0 → ℕ → ℝ≥0 := fun u n => (idx u n : ℝ≥0) * d n
  let b : ℝ≥0 → ℕ → ℝ≥0 :=
    fun u n => ((idx u n + 1 : ℕ) : ℝ≥0) * d n
  let E : ℕ → Finset ℝ≥0 := fun n =>
    (Finset.range (n + 1)).image (fun j => ((j + 1 : ℕ) : ℝ≥0) * d n)
  let left : ℕ → ℝ≥0 → ℝ≥0 := fun n t => t - d n
  have ha (u : ℝ≥0) (hu : u ∈ S) : Tendsto (a u) atTop (𝓝[<] u) :=
    (hspec u hu).2.1
  have hb (u : ℝ≥0) (hu : u ∈ S) :
      Tendsto (b u) atTop (nhdsWithin u (Ici u)) := (hspec u hu).2.2
  have hIn (u : ℝ≥0) (hu : u ∈ S) (n : ℕ) : b u n ∈ E n := by
    exact Finset.mem_image.mpr
      ⟨idx u n, Finset.mem_range.mpr (Nat.lt_succ_of_le ((hspec u hu).1 n).1), rfl⟩
  have hLeft (u : ℝ≥0) (_hu : u ∈ S) (n : ℕ) :
      left n (b u n) = a u n := by
    have hstep : b u n = a u n + d n := by
      dsimp [a, b]
      push_cast
      ring
    dsimp [left]
    rw [hstep]
    simp
  simpa only [E, left, d] using
    (avram_p2_34dbea70_all_negative_jump_mesh_liminf
      Y S a b E left ε hε ha hb hL hR hJump hIn hLeft)
