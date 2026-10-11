-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.dft_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:58.673121+00:00
-- url     : https://prove2.me/submissions/f6dc3e3c-b901-4b9a-85f0-64e9e84e012e

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.dft_mem_unitaryGroup
import Mathlib
import Definitions.Def_ChapterSternGerlach
import Theorems.Thm_BookProof_ChapterSternGerlach_dft_unitary
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) :
    dftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by

  rw [Matrix.mem_unitaryGroup_iff]
  exact dft_unitary n hn
