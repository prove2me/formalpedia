-- Prove2me | solution 1 for Everyday.higgs_square
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:23:25.204475+00:00
-- url     : https://prove2.me/submissions/be3a1d73-fb3a-4b3f-a6aa-bbbb2fd2f370

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

open Everyday
/-- Higgs: the Mexican-hat potential is a completed square —
-μ²|φ|² + λ|φ|⁴ equals λ(|φ|² - μ²/(2λ))² minus the floor μ⁴/(4λ).
The potential's shape is a hat: a quadratic bowl in |φ|² lifted by the
quartic, with its minimum value and its location read off the square.
The quartic coupling λ is bound as lam, λ being a reserved keyword in
Lean 4. -/


theorem solution (μ lam : ℝ) (φ : ℂ) (hlam : lam ≠ 0) :
    higgsV μ lam φ
      = -(μ ^ 4 / (4 * lam)) + lam * (Complex.normSq φ - μ ^ 2 / (2 * lam)) ^ 2 := by
  unfold higgsV; field_simp; ring


