-- Prove2me | solution 1 for BookProof.ChapterLorentzTranslation.gamma_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:21:23.810449+00:00
-- url     : https://prove2.me/submissions/dc5374d7-8e95-436c-b2fb-03bc40aec54b

-- Generated from ChapterLorentzTranslation.lean — solution of BookProof.ChapterLorentzTranslation.gamma_zero
import Mathlib
import Definitions.Def_ChapterLorentzTranslation
open BookProof.ChapterLorentzTranslation




open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : gamma (fun _ => 0) = 1 := by

  unfold gamma; simp
