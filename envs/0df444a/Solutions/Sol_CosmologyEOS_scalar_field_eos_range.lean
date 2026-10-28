-- Prove2me | solution 1 for CosmologyEOS.scalar_field_eos_range
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:10:10.50905+00:00
-- url     : https://prove2.me/submissions/53b02945-df00-4572-905b-80263bbde1a7

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

theorem solution :
    (∀ phiDot V : ℝ, 0 < phiDot ^ 2 / 2 + V → -1 ≤ scalarFieldEOS phiDot V) ∧
    (∀ phiDot V : ℝ, 0 ≤ V → 0 < phiDot ^ 2 / 2 + V → scalarFieldEOS phiDot V ≤ 1) ∧
    (∀ w ∈ Set.Icc (-1 : ℝ) 1, ∃ phiDot V : ℝ,
      0 ≤ V ∧ 0 < phiDot ^ 2 / 2 + V ∧ scalarFieldEOS phiDot V = w) := by
  refine ⟨fun x V h => ?_, fun x V hV h => ?_, fun w hw => ?_⟩
  · unfold scalarFieldEOS
    rw [le_div_iff₀ h]; nlinarith [sq_nonneg x]
  · unfold scalarFieldEOS
    rw [div_le_iff₀ h]; linarith
  · obtain ⟨h1, h2⟩ := hw
    refine ⟨Real.sqrt (1 + w), (1 - w) / 2, by linarith, ?_, ?_⟩
    · rw [Real.sq_sqrt (by linarith)]; linarith
    · unfold scalarFieldEOS
      rw [Real.sq_sqrt (by linarith)]
      have : (1 + w) / 2 + (1 - w) / 2 = 1 := by ring
      rw [this]; ring
