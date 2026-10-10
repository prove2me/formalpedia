-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.range_bFullR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:09:37.44613+00:00
-- url     : https://prove2.me/submissions/bd8a97ab-6c1c-4678-bf89-e56d52a46610

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.range_bFullR
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

set_option maxHeartbeats 1000000 in
theorem solution :
    Set.range bFullR
      = ((Set.range bHalfR ∪ Set.range b10R) ∪ Set.range bPsR) ∪ Set.range w2R := by

  ext x
  constructor
  · rintro ⟨y, rfl⟩
    fin_cases y <;> simp [bFullR, bHalfR, b10R, bPsR, w2R, bFull]
  · rintro (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
    · fin_cases y
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
    · fin_cases y
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨7, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨9, rfl⟩
    · fin_cases y
      · exact ⟨10, rfl⟩
      · exact ⟨11, rfl⟩
      · exact ⟨12, rfl⟩
      · exact ⟨13, rfl⟩
    · fin_cases y
      · exact ⟨14, rfl⟩
      · exact ⟨15, rfl⟩
