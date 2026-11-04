-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_all_negative_path_jumps_le_index_indicator_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:57:50.831741+00:00
-- url     : https://prove2.me/submissions/79642593-7fcc-49b1-a10f-de53b802cf9a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal ENat ENNReal BigOperators

/-- All original negative path jumps are controlled by indexed-cell liminf. -/
theorem solution (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (hTimes : ∀ u ∈ S, 0 < u ∧ u ≤ T)
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε) :
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      ∑ i ∈ Finset.range (n + 1),
        (if Y (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) < -ε / 2
          then (1 : ℕ∞) else 0)) atTop := by
  classical
  letI : DecidableEq ℝ≥0 := Classical.decEq _
  have hgrid : S.encard ≤ Filter.liminf (fun n : ℕ =>
      ((((Finset.range (n + 1)).image
        (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
        (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞))
        atTop := by
    exact avram_p2_34dbea70_actual_uniform_path_negative_jump_liminf
      Y S T hT ε hε hTimes hL hR hJump
  calc
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      ((((Finset.range (n + 1)).image
        (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
        (fun t : ℝ≥0 => Y t - Y (t - (T / ((n : ℝ≥0) + 1))) < -ε / 2)).card : ℕ∞))
        atTop := hgrid
    _ ≤ _ := by
      apply Filter.liminf_le_liminf
      filter_upwards [] with n
      have hn := avram_p2_34dbea70_original_uniform_grid_image_le_enat_indicator_count
        Y T n ε
      first
      | exact hn
      | simpa only [LE.le] using hn
      | simpa using hn
      | convert hn using 1 <;> simp
      all_goals
        first
        | exact ⟨⊥, Filter.Eventually.of_forall (fun _ => bot_le)⟩
        | exact ⟨⊤, fun a _ => le_top⟩
