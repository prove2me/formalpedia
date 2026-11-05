-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:08:07.072679+00:00
-- url     : https://prove2.me/submissions/3a48751c-6a21-457e-836d-c837e917125a

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At a capped original source cell, any nonnegative negative-jump
mass preserves the w region at the unshifted and shifted bases.
Thus the cap-linear mixed commutator equals the genuine w term. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (z c j : ℝ)
    (hz : C = ⊤ ∨ z ≤ C.toReal)
    (hup : C = ⊤ ∨ z + c ≤ C.toReal)
    (hj : 0 ≤ j) :
    let V : ℝ → ℝ := fun r =>
      if C = ⊤ then w r else if r ≤ C.toReal then w r
      else w C.toReal + (r - C.toReal)
    V (z + c - j) - V (z + c) - V (z - j) + V z =
      w (z + c - j) - w (z + c) - w (z - j) + w z := by
  intro V
  by_cases hTop : C = ⊤
  · simp [V, hTop]
  · have hzle : z ≤ C.toReal := hz.resolve_left hTop
    have huple : z + c ≤ C.toReal := hup.resolve_left hTop
    have hzj : z - j ≤ C.toReal := by linarith
    have hupj : z + c - j ≤ C.toReal := by linarith
    simp [V, hTop, hzle, huple, hzj, hupj]
