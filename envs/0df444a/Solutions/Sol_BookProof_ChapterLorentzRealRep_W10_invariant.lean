-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.W10_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:57:23.222259+00:00
-- url     : https://prove2.me/submissions/15934fa3-b485-461d-9b67-9b4e3a9b541e

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.W10_invariant
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_conj_inv_10
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_conjL_apply
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mem_W10
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) :
    W10.map (conjL (castR S) (castR (cinv S))) ≤ W10 := by

  apply Submodule.map_le_iff_le_comap.mpr
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  simp only [b10R, conjL_apply, Submodule.mem_comap, SetLike.mem_coe]
  convert castR_mem_W10 _ (conj_inv_10 S hS i) using 1
  simp [castR_mul]
