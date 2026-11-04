-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_all_negative_jump_mesh_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:22:21.898184+00:00
-- url     : https://prove2.me/submissions/34807b3b-668f-4077-b2df-a094e03906a2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_negative_jump_mesh_capture
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_subsets_liminf_encard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- All genuine negative jumps are captured in the limiting mesh count;
each finite selection is injected into genuine distinct negative cells. -/
theorem solution (Y : ℝ≥0 → ℝ) (S : Set ℝ≥0)
    (a b : ℝ≥0 → ℕ → ℝ≥0)
    (E : ℕ → Finset ℝ≥0) (left : ℕ → ℝ≥0 → ℝ≥0)
    (ε : ℝ) (hε : 0 < ε)
    (ha : ∀ u ∈ S, Tendsto (a u) atTop (𝓝[<] u))
    (hb : ∀ u ∈ S, Tendsto (b u) atTop (nhdsWithin u (Ici u)))
    (hL : ∀ u ∈ S, Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (hR : ∀ u ∈ S, ContinuousWithinAt Y (Ici u) u)
    (hJump : ∀ u ∈ S, Y u - Function.leftLim Y u ≤ -ε)
    (hIn : ∀ u ∈ S, ∀ n, b u n ∈ E n)
    (hLeft : ∀ u ∈ S, ∀ n, left n (b u n) = a u n) :
    S.encard ≤ Filter.liminf (fun n : ℕ =>
      (((E n).filter (fun t : ℝ≥0 =>
        Y t - Y (left n t) < -ε / 2)).card : ℕ∞)) atTop := by
  apply avram_p2_34dbea70_finite_subsets_liminf_encard S
    (fun n => ((E n).filter (fun t : ℝ≥0 =>
      Y t - Y (left n t) < -ε / 2)).card)
  intro F hFS
  exact avram_p2_34dbea70_finite_negative_jump_mesh_capture
    Y F a b E left ε hε
    (fun u hu => ha u (hFS hu))
    (fun u hu => hb u (hFS hu))
    (fun u hu => hL u (hFS hu))
    (fun u hu => hR u (hFS hu))
    (fun u hu => hJump u (hFS hu))
    (fun u hu => hIn u (hFS hu))
    (fun u hu => hLeft u (hFS hu))
