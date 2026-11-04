-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_finite_negative_jump_mesh_capture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:03:27.676506+00:00
-- url     : https://prove2.me/submissions/617295b6-ac47-4163-9157-debcecb18dda

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_straddling_cell_detects_negative_jump
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- A finite family of original negative jumps is eventually counted by
distinct straddling mesh cells, without finite-activity assumptions. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (F : Finset ℝ≥0)
    (a b : ℝ≥0 → ℕ → ℝ≥0)
    (E : ℕ → Finset ℝ≥0) (left : ℕ → ℝ≥0 → ℝ≥0)
    (ε : ℝ) (hε : 0 < ε)
    (ha : ∀ u ∈ F, Tendsto (a u) atTop (𝓝[<] u))
    (hb : ∀ u ∈ F, Tendsto (b u) atTop (nhdsWithin u (Ici u)))
    (hL : ∀ u ∈ F, Tendsto Y (𝓝[<] u)
      (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ F, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ F, Y u - Function.leftLim Y u ≤ -ε)
    (hIn : ∀ u ∈ F, ∀ n, b u n ∈ E n)
    (hLeft : ∀ u ∈ F, ∀ n, left n (b u n) = a u n) :
    ∀ᶠ n : ℕ in atTop,
      F.card ≤ ((E n).filter
        (fun t : ℝ≥0 => Y t - Y (left n t) < -ε / 2)).card := by
  classical
  have hDetect : ∀ᶠ n : ℕ in atTop, ∀ u ∈ F,
      Y (b u n) - Y (a u n) < -ε / 2 := by
    apply (Filter.eventually_all_finset F).2
    intro u hu
    exact avram_p2_34dbea70_straddling_cell_detects_negative_jump
      Y u (a u) (b u) (ha u hu) (hb u hu)
        (hL u hu) (hR u hu) ε hε (hJump u hu)
  have hbn : ∀ u ∈ F, Tendsto (b u) atTop (𝓝 u) := by
    intro u hu
    exact (hb u hu).mono_right nhdsWithin_le_nhds
  have hInj : ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun u : ℝ≥0 => b u n) (F : Set ℝ≥0) :=
    avram_p2_34dbea70_finite_distinct_time_endpoints_eventually_injective F b hbn
  filter_upwards [hDetect, hInj] with n hd hi
  apply Finset.card_le_card_of_injOn (fun u : ℝ≥0 => b u n)
  · intro u hu
    exact Finset.mem_filter.mpr
      ⟨hIn u hu n, by simpa only [hLeft u hu n] using hd u hu⟩
  · exact hi
