-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_massless_lorentz
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:53:30.837197+00:00
-- url     : https://prove2.me/submissions/17531ce9-0ca0-4863-858e-1a8ad75ddd1d

-- Generated from ChapterA4d.lean — solution of BookProof.ChapterA3.upsilon_massless_lorentz
import Mathlib
import Definitions.Def_ChapterA4d
import Theorems.Thm_BookProof_ChapterA3_fixesNullAxis_iff_conj
import Theorems.Thm_BookProof_ChapterA3_nullConj_iff_form
import Theorems.Thm_BookProof_ChapterA3_upsilon_mem_lorentz
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T ∈ SEtwo) :
    Upsilon T ∈ LorentzO ∧ FixesNullAxis (Upsilon T) := by

  obtain ⟨hd, hb, ha⟩ := hT
  exact ⟨upsilon_mem_lorentz T hd,
    (fixesNullAxis_iff_conj T).mpr ((nullConj_iff_form T).mpr ⟨hb, ha⟩)⟩
