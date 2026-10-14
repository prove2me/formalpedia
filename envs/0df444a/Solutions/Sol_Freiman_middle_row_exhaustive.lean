-- Prove2me | solution 1 for Freiman.middle_row_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-09T20:02:37.226544+00:00
-- url     : https://prove2.me/submissions/e941d21a-80ef-4052-a3db-148e9918d6dc

import Definitions.Def_Freiman_middleRoots

open Freiman

theorem solution : ∀ c : MiddleCore, ∃ r : MiddleRow, middleRowCondition c r := by
  intro c
  by_cases hsame :
      (middleNormalized c).left.length % 2 = (middleNormalized c).right.length % 2
  · rcases lt_or_ge (middleA c (549 / 1000)) (middleQ c) with hA | hA
    · by_cases hs1 : middleShort c 1
      · exact ⟨.equalIShort, hsame, hA, hs1⟩
      · exact ⟨.equalIJ, hsame, hA, hs1⟩
    · rcases lt_or_ge (middleQ c) (middleB c (313 / 1000)) with hB | hB
      · exact ⟨.equalIIa, hsame, hA, hB⟩
      · by_cases hs2 : middleShort c 2
        · by_cases hs1 : middleShort c 1
          · exact ⟨.equalIIbShort, hsame, hA, hB, hs2, hs1⟩
          · exact ⟨.equalIIbJ, hsame, hA, hB, hs2, hs1⟩
        · exact ⟨.equalIIbNormal, hsame, hA, hB, hs2⟩
  · rcases lt_or_ge (middleA c (55 / 100)) (middleQ c) with hA | hA
    · exact ⟨.mixedA, hsame, hA⟩
    · rcases lt_or_ge (middleQ c) (middleB c (328 / 1000)) with hB | hB
      · exact ⟨.mixedB, hsame, hA, hB⟩
      · exact ⟨.mixedC, hsame, hA, hB⟩
