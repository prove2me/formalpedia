-- Prove2me | solution 1 for Freiman.middleRepair_frame_path_realized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:22.627862+00:00
-- url     : https://prove2.me/submissions/0b2f0e57-95bd-4826-aadf-fe0b15913db3

import Theorems.Thm_Freiman_middleRepair_frame_nested_completion
import Theorems.Thm_Freiman_middleRepair_frame_oscillation
import Theorems.Thm_Freiman_middleRepair_frame_start_physical
import Theorems.Thm_Freiman_middleRepair_path_mesh
import Theorems.Thm_Freiman_middle_zero_limit_bound
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore) (s : ℕ → MiddleRepairFrame),
  middleRepairPath c t p → middleRepairLift c t p s → middleRealized c t := by
  intro c t p s hp hs
  obtain ⟨a,ha⟩ := middleRepair_frame_nested_completion c t s hs.1
  have hb : ∀ n : ℕ, |localValue a 0-t| ≤ middleWidth (p n).left+middleWidth (p n).right := by
    intro n
    have h := middleRepair_frame_oscillation (s n) a t (hs.1.2 n).2.1 (ha n) (hs.1.2 n).2.2.2.1
    simpa only [hs.2 n] using h
  have heq := middle_zero_limit_bound (localValue a 0-t) _ hb (middleRepair_path_mesh c t p hp)
  refine ⟨a,?_,sub_eq_zero.mp heq⟩
  have h0 := ha 0
  rw [hs.1.1,middleRepair_frame_start_physical] at h0
  exact h0
