-- Prove2me | solution 2 for CohnElkies.upperGammaVarianceDensity_pointwise_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:54.923786+00:00
-- url     : https://prove2.me/submissions/51684f53-f386-4054-b86d-87d70adfbfb3

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * Real.exp (-η * a) ≤
      a ^ 2 * upperGammaMeasureDensity ℓ η a ∧
    a ^ 2 * upperGammaMeasureDensity ℓ η a ≤
      (a + ℓ / 2) * Real.exp (-η * a) := by
  have hx : 0 < 2 * a / ℓ := by positivity
  set x := 2 * a / ℓ with hxdef
  have hax : a = x * ℓ / 2 := by rw [hxdef]; field_simp
  set E := Real.exp (-x) with hEdef
  have hE1 : E < 1 := by rw [hEdef, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hD : 0 < 1 - E := by linarith
  have h1 : 1 - x ≤ E := by have := Real.add_one_le_exp (-x); linarith
  have h2 : (x + 1) * E ≤ 1 := by
    have h := Real.add_one_le_exp x
    have : Real.exp x * E = 1 := by rw [hEdef, ← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-x)]
  have key : a ^ 2 * upperGammaMeasureDensity ℓ η a = (a / (1 - E)) * Real.exp (-η * a) := by
    unfold upperGammaMeasureDensity
    rw [← hxdef, ← hEdef]
    field_simp
  rw [key]
  have he := (Real.exp_pos (-η * a)).le
  constructor
  · apply mul_le_mul_of_nonneg_right _ he
    rw [le_div_iff₀ hD, hax]
    nlinarith [mul_le_mul_of_nonneg_left h1 hℓ.le]
  · apply mul_le_mul_of_nonneg_right _ he
    rw [div_le_iff₀ hD, hax]
    nlinarith [mul_le_mul_of_nonneg_left h2 hℓ.le]

