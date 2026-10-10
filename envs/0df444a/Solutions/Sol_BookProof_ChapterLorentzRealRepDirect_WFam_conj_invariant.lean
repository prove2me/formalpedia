-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:59:34.043081+00:00
-- url     : https://prove2.me/submissions/e5e95e4c-af96-421e-a936-83375fcda410

-- Generated from ChapterLorentzRealRepDirect.lean — solution of BookProof.ChapterLorentzRealRepDirect.WFam_conj_invariant
import Mathlib
import Definitions.Def_ChapterLorentzRealRepDirect
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_WTwo_invariant
import Theorems.Thm_BookProof_ChapterLorentzRealRep_W10_invariant
import Theorems.Thm_BookProof_ChapterLorentzRealRep_WHalf_invariant
import Theorems.Thm_BookProof_ChapterLorentzRealRep_WPs_invariant
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRepDirect



open Matrix Module


open BookProof.ChapterLorentzRealRep BookProof.ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull
open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega) (i : Fin 4) :
    (WFam i).map (conjL (castR S) (castR (cinv S))) ≤ WFam i := by

  fin_cases i <;> simp only [WFam, 
    ]
  · exact WHalf_invariant S hS
  · exact W10_invariant S hS
  · exact WPs_invariant S hS
  · exact WTwo_invariant S hS
