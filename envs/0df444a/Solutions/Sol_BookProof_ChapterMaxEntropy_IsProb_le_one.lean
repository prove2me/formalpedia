-- Prove2me | solution 1 for BookProof.ChapterMaxEntropy.IsProb.le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:53:14.758261+00:00
-- url     : https://prove2.me/submissions/30b7d68e-4637-4b74-81b8-eff26c9c3a97

-- Generated from ChapterMaxEntropy.lean — solution of BookProof.ChapterMaxEntropy.IsProb.le_one
import Mathlib
import Definitions.Def_ChapterMaxEntropy
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterMaxEntropy



open Real BigOperators Finset


variable {α : Type*} [Fintype α]

variable {α : Type*} [Fintype α]

set_option maxHeartbeats 1000000 in
theorem solution {p : α → ℝ} (hp : IsProb p) (i : α) : p i ≤ 1 := by

  rw [← hp.sum_one]
  exact Finset.single_le_sum (fun j _ => hp.nonneg j) (Finset.mem_univ i)
