-- Prove2me | solution 1 for BookProof.ChapterA3.massless_little_group
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:52:43.612894+00:00
-- url     : https://prove2.me/submissions/c2c1f0f0-382c-402a-bb5d-d02c3b2a560d

-- Generated from ChapterA4d.lean — solution of BookProof.ChapterA3.massless_little_group
import Mathlib
import Definitions.Def_ChapterA4d
import Theorems.Thm_BookProof_ChapterA3_fixesNullAxis_iff_conj
import Theorems.Thm_BookProof_ChapterA3_nullConj_iff_form
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution :
    {T : Matrix (Fin 2) (Fin 2) ℂ | T.det = 1 ∧ FixesNullAxis (Upsilon T)} = SEtwo := by

  ext T
  simp only [Set.mem_setOf_eq, SEtwo]
  constructor
  · rintro ⟨hd, hf⟩
    obtain ⟨hb, ha⟩ := (nullConj_iff_form T).mp ((fixesNullAxis_iff_conj T).mp hf)
    exact ⟨hd, hb, ha⟩
  · rintro ⟨hd, hb, ha⟩
    exact ⟨hd, (fixesNullAxis_iff_conj T).mpr ((nullConj_iff_form T).mpr ⟨hb, ha⟩)⟩
