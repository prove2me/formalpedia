-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.range_bAllR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:18:38.65752+00:00
-- url     : https://prove2.me/submissions/eb16f2ca-8d91-4f25-89b7-05b7649f5a3d

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.range_bAllR
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution :
    Set.range bAllR = Set.range bHalfR ∪ Set.range b10R ∪ Set.range bPsR := by

  ext x;
  constructor;
  · rintro ⟨ y, rfl ⟩;
    fin_cases y <;> simp [ bAllR, bHalfR, b10R, bPsR, bAll ];
  · rintro ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩)
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
