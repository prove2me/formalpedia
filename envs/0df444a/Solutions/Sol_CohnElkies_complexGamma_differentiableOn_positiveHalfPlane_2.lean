-- Prove2me | solution 2 for CohnElkies.complexGamma_differentiableOn_positiveHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:04:38.975362+00:00
-- url     : https://prove2.me/submissions/3bdc9088-ad62-42af-b295-fdd1a89d664e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution :
    DifferentiableOn ℂ Complex.Gamma
      {z : ℂ | 0 < z.re} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply Complex.differentiableAt_Gamma
  intro m h
  have := congrArg Complex.re h
  simp at this
  simp only [Set.mem_setOf_eq] at hz
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

