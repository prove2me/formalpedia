-- Prove2me | solution 1 for AvramDividend.Classical.chat03_positive_cutoff_makes_quadratic_error_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:13:37.549118+00:00
-- url     : https://prove2.me/submissions/98da3294-daa5-4b6e-92f0-c340c0d0c494

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
/-!
For any nonnegative second-moment bound and positive tolerance,
a positive truncation threshold makes C/R small enough.
-/
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ C / R ≤ ε := by
  have hC1 : 0 < C + 1 := by linarith
  let R := (C + 1) / ε
  have hR : 0 < R := div_pos hC1 hε
  refine ⟨R, hR, ?_⟩
  apply (div_le_iff₀ hR).2
  have hmul : ε * R = C + 1 := by
    dsimp [R]
    field_simp [ne_of_gt hε]
  linarith
