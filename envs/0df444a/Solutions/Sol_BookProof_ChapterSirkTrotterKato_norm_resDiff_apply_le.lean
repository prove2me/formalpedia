-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.norm_resDiff_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:16:01.445057+00:00
-- url     : https://prove2.me/submissions/3bb64787-f53b-4763-9b7d-d01febf1739c

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.norm_resDiff_apply_le
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (y : H) : ‖resDiff T S n y‖ ≤ 2 * ‖y‖ := by

  have h1 : ‖T.resCLM 1 y‖ ≤ ‖y‖ := by
    have := T.norm_resCLM_apply_le 1 y
    simpa using this
  have h2 : ‖(S n).resCLM 1 y‖ ≤ ‖y‖ := by
    have := (S n).norm_resCLM_apply_le 1 y
    simpa using this
  have : ‖resDiff T S n y‖ ≤ ‖T.resCLM 1 y‖ + ‖(S n).resCLM 1 y‖ := by
    simpa [resDiff] using norm_sub_le (T.resCLM 1 y) ((S n).resCLM 1 y)
  linarith
