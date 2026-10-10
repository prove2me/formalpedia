-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:03:55.854252+00:00
-- url     : https://prove2.me/submissions/52bb22a8-05cc-4a0c-ab76-0385e49e641e

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_injective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal


@[simp] private theorem dissipative_apply (x : ℝ) : dissipative x = x / 2 := rfl

set_option maxHeartbeats 1000000 in
theorem solution : Function.Injective dissipative := by

  intro a b h
  simp only [dissipative_apply] at h
  linarith
