-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_little_group_lorentz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:52:00.559229+00:00
-- url     : https://prove2.me/submissions/ae025880-e580-4bd8-98d0-d113462bab47

-- Generated from ChapterA4c.lean — solution of BookProof.ChapterA3.upsilon_little_group_lorentz
import Mathlib
import Definitions.Def_ChapterA4c
import Theorems.Thm_BookProof_ChapterA3_fixesTimeAxis_iff_unitary
import Theorems.Thm_BookProof_ChapterA3_upsilon_mem_lorentz
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T ∈ SUtwo) :
    Upsilon T ∈ LorentzO ∧ FixesTimeAxis (Upsilon T) := by

  obtain ⟨hd, hu⟩ := hT
  exact ⟨upsilon_mem_lorentz T hd, (fixesTimeAxis_iff_unitary T).mpr hu⟩
