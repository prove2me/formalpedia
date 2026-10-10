-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:04:39.426731+00:00
-- url     : https://prove2.me/submissions/2a19a8eb-cc2c-49e9-a594-efed2a80337e

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_not_surjective_unitInterval
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal


@[simp] private theorem dissipative_apply (x : ℝ) : dissipative x = x / 2 := rfl

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ y ∈ Set.Icc (0 : ℝ) 1, y ∉ dissipative '' Set.Icc (0 : ℝ) 1 := by

  refine ⟨1, by norm_num, ?_⟩
  rintro ⟨x, hx, hxy⟩
  simp only [Set.mem_Icc, dissipative_apply] at hx hxy
  linarith [hx.2]
