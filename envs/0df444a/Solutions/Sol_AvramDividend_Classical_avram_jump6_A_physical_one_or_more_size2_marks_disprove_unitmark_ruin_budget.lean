-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_physical_one_or_more_size2_marks_disprove_unitmark_ruin_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:29:25.734772+00:00
-- url     : https://prove2.me/submissions/d63d693a-8117-42ee-804e-60071e62748a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
noncomputable section
theorem solution
    (b t B : ℝ) (N : ℕ)
    (hb : b ≤ 1 / 4000) (ht : t ≤ 1 / 500)
    (hMark : 1 ≤ N) (hB : B ≤ 0)
    (hLedger : 0 ≤ (111 / 100 : ℝ) + b - 2 * (N : ℝ) + 2 * t + B) :
    False := by
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMark
  linarith
