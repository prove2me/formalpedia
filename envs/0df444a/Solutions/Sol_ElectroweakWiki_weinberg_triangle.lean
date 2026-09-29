-- Prove2me | solution 1 for ElectroweakWiki.weinberg_triangle
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:42:13.694615+00:00
-- url     : https://prove2.me/submissions/cc2a707b-741c-41b8-bfa5-2e557da61f8e

import Definitions.Def_ElectroweakWiki_defs
import Mathlib.Tactic.FieldSimp

theorem solution (g g' : ℝ) (hg : 0 < g) (hg' : 0 < g') :
    Real.cos (ElectroweakWiki.weinbergAngle g g') =
        g / Real.sqrt (g ^ 2 + g' ^ 2) ∧
      Real.sin (ElectroweakWiki.weinbergAngle g g') =
        g' / Real.sqrt (g ^ 2 + g' ^ 2) := by
  let S := Real.sqrt (1 + (g' / g) ^ 2)
  let R := Real.sqrt (g ^ 2 + g' ^ 2)
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hSpos : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hRpos : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hS2 : S ^ 2 = 1 + (g' / g) ^ 2 := Real.sq_sqrt (by positivity)
  have hR2 : R ^ 2 = g ^ 2 + g' ^ 2 := Real.sq_sqrt (by positivity)
  have hsq : (g * S) ^ 2 = R ^ 2 := by
    rw [mul_pow, hS2, hR2]
    field_simp [hg0]
  have hkey : g * S = R := by
    nlinarith [mul_pos hg hSpos]
  unfold ElectroweakWiki.weinbergAngle
  rw [Real.cos_arctan, Real.sin_arctan]
  constructor
  · change 1 / S = g / R
    rw [← hkey]
    field_simp [hg0, ne_of_gt hSpos]
  · change (g' / g) / S = g' / R
    rw [← hkey]
    field_simp [hg0, ne_of_gt hSpos]

#print axioms solution
