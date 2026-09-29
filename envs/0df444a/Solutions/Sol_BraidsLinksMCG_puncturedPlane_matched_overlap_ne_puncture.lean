-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_matched_overlap_ne_puncture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T09:04:31.798818+00:00
-- url     : https://prove2.me/submissions/a513874a-3123-4ecb-8dfb-f5c38e9b3767

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open Set
open BraidsLinksMCG

/-- The overlap lower bound `n + 1 - 3/4 < j + 1` together with `j < n + 1` forces
`j = n`: the bound puts `j` above `n - 7/4`, so the only integer strictly below
`n + 1` that satisfies it is `n` itself. -/
private lemma index_eq_of_overlap_lower (n : ℕ) (j : Fin (n + 1))
    (hlo : (n : ℝ) + 1 - 3 / 4 < (((j : ℕ) + 1 : ℕ) : ℂ).re) : j = n := by
  have hre : (((j : ℕ) + 1 : ℕ) : ℂ).re = (j : ℝ) + 1 := by
    simp [Nat.cast_add, Nat.cast_one]
  have hloR : (n : ℝ) + 1 - 3 / 4 < (j : ℝ) + 1 := by
    rw [hre] at hlo
    exact hlo
  -- The bound carries a fractional offset, so it is NOT a `ℕ` inequality: casting it
  -- directly leaves `↑(n+1) - 3/4` and `mod_cast` cannot discharge that term.
  -- The fraction is absorbed in `ℝ` first, where `3/4 < 1` gives a clean strict
  -- bound, and only the fraction-free inequality is transported to `ℕ`.
  have hpos : (n : ℝ) < (j : ℝ) + 1 := by linarith
  have hfloor : n < j + 1 := by
    exact_mod_cast hpos
  have hltj : j < n + 1 := j.isLt
  omega

/-- No point of the matched-cover overlap is a puncture.  A puncture is the real
point `j + 1` with `j < n + 1`; the overlap's real part is `> n + 1 - 3/4`, which
pins `j = n`, and the real point `n + 1` satisfies none of the three cap disjuncts.

This is `BraidsLinksMCG.puncturedPlane_matched_overlap_ne_puncture`. -/
theorem solution (n : ℕ) (j : Fin (n + 1))
    (hlo : (n : ℝ) + 1 - 3 / 4 < (((j : ℕ) + 1 : ℕ) : ℂ).re)
    (hcap : (((j : ℕ) + 1 : ℕ) : ℂ).re < (n : ℝ) + 1 ∨ 0 < (((j : ℕ) + 1 : ℕ) : ℂ).im ∨
      dist (((j : ℕ) + 1 : ℕ) : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) : False := by
  rw [index_eq_of_overlap_lower n j hlo] at hcap
  -- `Complex.natCast_re` and `Complex.natCast_im` are both `[simp]` and hold by
  -- `rfl`, so the three real facts about the point `(n+1 : ℕ)` are read off directly.
  have hre : (((n : ℕ) + 1 : ℕ) : ℂ).re = (n : ℝ) + 1 := by
    simp [Nat.cast_add, Nat.cast_one]
  have him0 : (((n : ℕ) + 1 : ℕ) : ℂ).im = 0 := by simp
  have hreA : ((n + 2 : ℕ) : ℂ).re = ((n + 2 : ℕ) : ℝ) := by
    simp [Nat.cast_add, Nat.cast_one]
  have himA : ((n + 2 : ℕ) : ℂ).im = 0 := by simp
  rcases hcap with hlt | him | hdist
  · -- `rw` normalises the real part while rewriting, so one application already
    -- turns `hlt` into the reflexive inequality `n + 1 < n + 1`; a second `rw`
    -- would then have no `(↑(n+1)).re` left to match.  The residual is a REAL
    -- reflexive inequality, so `linarith` is the right terminal solver here;
    -- `omega` only sees `Nat`/`Int` atoms and reports "no usable constraints".
    rw [hre] at hlt
    linarith
  · rw [him0] at him
    exact absurd him (by norm_num)
  · -- Both points are real, so the distance reduces to a real distance.  The anchor
    -- `n + 2` is exactly one to the right of the puncture `n + 1`, so the distance
    -- is `1`, contradicting the required `dist < 1/2`.
    rw [Complex.dist_of_im_eq (by rw [him0, himA])] at hdist
    rw [hre, hreA] at hdist
    rw [Real.dist_eq, abs_lt] at hdist
    -- `abs_lt` gives `-1/2 < (n+1)-(n+2) ∧ (n+1)-(n+2) < 1/2`.  Only the FIRST
    -- conjunct is contradictory (the second is true), so it alone is used.
    obtain ⟨h₁, -⟩ := hdist
    push_cast at h₁
    linarith
