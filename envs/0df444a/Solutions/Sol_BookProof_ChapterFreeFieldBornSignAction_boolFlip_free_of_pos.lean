-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:18:40.994278+00:00
-- url     : https://prove2.me/submissions/b4069485-f7f2-4fb9-aede-b1966db185ac

-- Generated from ChapterFreeFieldBornSignAction.lean — solution of BookProof.ChapterFreeFieldBornSignAction.boolFlip_free_of_pos
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignAction_boolFlip_eq_self_iff
open BookProof.ChapterFreeFieldBornSignAction



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {b : Fin n → Bool} {x : EuclideanSpace ℝ (Fin n)}
    (hx : ∀ k, x k ≠ 0) :
    boolFlip b x = x ↔ b = (fun _ => false) := by

  rw [boolFlip_eq_self_iff]; aesop
