-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.exists_mixed_state_both
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:56.181445+00:00
-- url     : https://prove2.me/submissions/a7be32ef-2ad1-4327-9b9b-76c2e7b3318a

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.exists_mixed_state_both
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
import Theorems.Thm_BookProof_ChapterGleasonPureMixed_halfI_isMixed
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ,
    IsMixedState ρ ∧ E ρ P0 = 1/2 ∧ E ρ Q = 1/2 := by

  refine ⟨(1/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ), halfI_isMixed, ?_, ?_⟩
  · simp [E, P0, Matrix.trace, Fin.sum_univ_two]
  · simp [E, Q, Matrix.trace, Fin.sum_univ_two]; norm_num
