-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_image_Icc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:04:40.47912+00:00
-- url     : https://prove2.me/submissions/46d63738-23e0-423a-a2dd-1b6c5e1a4fa7

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_image_Icc
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal


@[simp] private theorem dissipative_apply (x : ℝ) : dissipative x = x / 2 := rfl

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    dissipative '' Set.Icc a b = Set.Icc (a / 2) (b / 2) := by

  ext y
  simp only [dissipative_apply, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨2 * y, ⟨by linarith, by linarith⟩, by ring⟩
