-- Prove2me | solution 1 for FamousTheorems.continuous_tsum
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.449428+00:00
-- url     : https://prove2.me/submissions/c7b5b27c-4256-4808-aa4a-104506ad7ac4

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {β : Type u_2} {F : Type u_3} [inst : NormedAddCommGroup F] [CompleteSpace F] 
    {u : α → ℝ} [inst_2 : TopologicalSpace β] {f : α → β → F}, 
    (∀ (i : α), Continuous (f i)) → 
    Summable u → (∀ (n : α) (x : β), ‖f n x‖ ≤ u n) → Continuous fun x => ∑' (n : α), f n x :=
  @_root_.continuous_tsum
