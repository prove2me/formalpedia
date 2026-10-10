-- Prove2me | solution 1 for BookProof.ChapterIrreversible.bornDist_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:14:14.153023+00:00
-- url     : https://prove2.me/submissions/9655422f-4c10-423f-bd37-0645689f7506

-- Generated from ChapterIrreversible.lean — solution of BookProof.ChapterIrreversible.bornDist_sum
import Mathlib
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterIrreversible



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin n → ℂ) (hv : ∑ a, ‖v a‖ ^ 2 = 1) :
    ∑ a, bornDist v a = 1 := by

  exact hv
