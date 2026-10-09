-- Prove2me | solution 1 for BookProof.ChapterGleasonPureMixed.exists_pure_expP0
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:47:26.944989+00:00
-- url     : https://prove2.me/submissions/d366f9ca-24df-49cf-9f73-9d8b43cc6476

-- Generated from ChapterGleasonPureMixed.lean — solution of BookProof.ChapterGleasonPureMixed.exists_pure_expP0
import Mathlib
import Definitions.Def_ChapterGleasonPureMixed
import Theorems.Thm_BookProof_ChapterGleasonPureMixed_Q_isPure
import Theorems.Thm_BookProof_ChapterGleasonPureMixed_E_Q_P0
open BookProof.ChapterGleasonPureMixed



open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : ∃ ρ : Matrix (Fin 2) (Fin 2) ℝ,
    IsPureState ρ ∧ E ρ P0 = 1/2 := ⟨Q, Q_isPure, E_Q_P0⟩
