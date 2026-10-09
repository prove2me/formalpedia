-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.exists_pure_expQ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:39.607113+00:00
-- url     : https://prove2.me/submissions/df59284d-3ad8-4d4e-93bc-194b25701265

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.exists_pure_expQ
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
import Theorems.Thm_BookProof_ChapterGleasonPureMixed_P0_isPure
import Theorems.Thm_BookProof_ChapterGleasonPureMixed_E_P0_Q
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ,
    IsPureState ρ ∧ E ρ Q = 1/2 := ⟨P0, P0_isPure, E_P0_Q⟩
