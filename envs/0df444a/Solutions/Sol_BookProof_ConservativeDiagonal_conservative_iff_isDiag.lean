-- Prove2me | solution 1 for BookProof.ConservativeDiagonal.conservative_iff_isDiag
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:45:24.155172+00:00
-- url     : https://prove2.me/submissions/075dbb29-1042-4e8e-be9f-f0066ad1918b

-- Generated from ChapterConservativeDiagonal.lean — solution of BookProof.ConservativeDiagonal.conservative_iff_isDiag
import Mathlib
import Definitions.Def_ChapterConservativeDiagonal
import Theorems.Thm_BookProof_ConservativeDiagonal_bracket_eventProj_apply
open BookProof.ConservativeDiagonal



open scoped Matrix
open Matrix BookProof.FreeFieldConstraint


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) :
    (∀ S T : Finset n, bracket (bracket H (eventProj S)) (eventProj T) = 0) ↔ H.IsDiag := by

  constructor
  · intro h k l hkl
    have h2 := congrFun (congrFun (h {k} {l}) k) l
    simp only [bracket_eventProj_apply, Matrix.zero_apply, Finset.mem_singleton] at h2
    have hlk : ¬ (l = k) := fun e => hkl e.symm
    have hkl' : ¬ (k = l) := hkl
    simp only [hkl', hlk, if_true, if_false] at h2
    simpa using h2
  · intro hdiag S T
    ext k l
    simp only [bracket_eventProj_apply, Matrix.zero_apply]
    by_cases hkl : k = l
    · subst hkl; ring
    · rw [hdiag hkl]; ring
