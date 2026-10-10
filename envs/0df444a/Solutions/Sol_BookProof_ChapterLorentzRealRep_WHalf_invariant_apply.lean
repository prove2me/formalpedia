-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.WHalf_invariant_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:57:41.664176+00:00
-- url     : https://prove2.me/submissions/a6b9b22e-e6e1-4d92-b9c4-63387e1bd0a2

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.WHalf_invariant_apply
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_conjL_apply
import Theorems.Thm_BookProof_ChapterLorentzRealRep_WHalf_invariant
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (S : Matrix (Fin 4) (Fin 4) ℤ) (hS : S ∈ Omega)
    (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : A ∈ WHalf) :
    castR S * A * castR (cinv S) ∈ WHalf := by

  have := WHalf_invariant S hS (Submodule.mem_map_of_mem hA)
  rwa [conjL_apply] at this
