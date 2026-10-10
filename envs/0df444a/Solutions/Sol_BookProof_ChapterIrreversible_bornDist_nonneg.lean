-- Prove2me | solution 1 for BookProof.ChapterIrreversible.bornDist_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:13:41.436683+00:00
-- url     : https://prove2.me/submissions/6662b691-2dd2-4c9f-a5b8-b866a4b34b45

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.bornDist_nonneg
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℂ) (a : Fin n) : 0 ≤ bornDist v a := by

  exact sq_nonneg _
