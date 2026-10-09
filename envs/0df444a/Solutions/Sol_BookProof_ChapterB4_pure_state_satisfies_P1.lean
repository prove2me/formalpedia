-- Prove2me | solution 1 for BookProof.ChapterB4.pure_state_satisfies_P1
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:45:33.285846+00:00
-- url     : https://prove2.me/submissions/f12a555e-81cc-4a5d-845b-a4ab10bc8f1d

-- Generated from ChapterB4.lean — solution of BookProof.ChapterB4.pure_state_satisfies_P1
import Mathlib
import Definitions.Def_ChapterB4
import Theorems.Thm_BookProof_ChapterB4_P2_isPureState
open BookProof.ChapterB4




open Matrix

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ ρ, IsPureState ρ ∧ Matrix.trace (ρ * P1) = 1 / 2 := by

  refine ⟨P2, P2_isPureState, ?_⟩
  simp [P1, P2, Matrix.trace_fin_two]
