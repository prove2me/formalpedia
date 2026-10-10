-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.WPs_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:57:37.796977+00:00
-- url     : https://prove2.me/submissions/c3410604-41ba-4d52-9e87-788d1b5ec7d6

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.WPs_invariant
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_conj_inv_ps
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_conjL_apply
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mem_WPs
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) :
    WPs.map (conjL (castR S) (castR (cinv S))) ≤ WPs := by

  apply Submodule.map_le_iff_le_comap.mpr
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  simp only [bPsR, conjL_apply, Submodule.mem_comap, SetLike.mem_coe]
  convert castR_mem_WPs _ (conj_inv_ps S hS i) using 1
  simp [castR_mul]
