-- Prove2me | solution 1 for ElectroweakWiki.elemCharge_eq_g_sin_eq_gp_cos
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T08:48:32.222187+00:00
-- url     : https://prove2.me/submissions/5a0c1096-0bd6-4e4e-9d05-81b403685ccc

import Definitions.Def_ElectroweakWiki_defs
import Mathlib.Tactic.FieldSimp

theorem solution (g g' : ℝ) (hg : 0 < g) (hg' : 0 < g') :
    ElectroweakWiki.elemCharge g g' =
        g * Real.sin (ElectroweakWiki.weinbergAngle g g') ∧
      ElectroweakWiki.elemCharge g g' =
        g' * Real.cos (ElectroweakWiki.weinbergAngle g g') := by
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
  unfold ElectroweakWiki.elemCharge ElectroweakWiki.weinbergAngle
  rw [Real.sin_arctan, Real.cos_arctan]
  constructor
  · change g * g' / R = g * ((g' / g) / S)
    rw [← hkey]
    field_simp [hg0, ne_of_gt hSpos]
  · change g * g' / R = g' * (1 / S)
    rw [← hkey]
    field_simp [hg0, ne_of_gt hSpos]

#print axioms solution
