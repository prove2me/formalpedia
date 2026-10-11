-- Prove2me | solution 1 for BookProof.ChapterSternGerlach.exists_uniform_unitary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:59:59.661989+00:00
-- url     : https://prove2.me/submissions/e3a0d7aa-5e5f-4d6a-a0e5-2592705546d8

-- Generated from ChapterSternGerlach.lean — solution of BookProof.ChapterSternGerlach.exists_uniform_unitary
import Mathlib
import Definitions.Def_ChapterSternGerlach
import Theorems.Thm_BookProof_ChapterSternGerlach_dft_normSq
import Theorems.Thm_BookProof_ChapterSternGerlach_dft_mem_unitaryGroup
open BookProof.ChapterSternGerlach




open Complex Matrix Finset

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ i j : Fin n, Complex.normSq (U i j) = 1 / n := ⟨dftMatrix n, dft_mem_unitaryGroup n hn, fun i j => dft_normSq n hn i j⟩
