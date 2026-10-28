-- Prove2me | solution 1 for CosmologyEOS.scalar_field_limiting_cases
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:09:37.523802+00:00
-- url     : https://prove2.me/submissions/266f7303-cb76-46f9-9e64-b63b391fa7cb

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

theorem solution :
    (∀ phiDot : ℝ, phiDot ≠ 0 → scalarFieldEOS phiDot 0 = 1) ∧
    (∀ V : ℝ, V ≠ 0 → scalarFieldEOS 0 V = -1) := by
  refine ⟨fun x hx => ?_, fun V hV => ?_⟩
  · unfold scalarFieldEOS
    have : x ^ 2 / 2 ≠ 0 := by positivity
    simp [div_self this]
  · unfold scalarFieldEOS
    simp [neg_div, div_self hV]
