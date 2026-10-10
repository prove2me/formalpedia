-- Prove2me | solution 1 for BookProof.LorentzOrthochronous.isPO_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:55:21.552903+00:00
-- url     : https://prove2.me/submissions/b891656f-5f39-4a69-9935-a3dbb1f96bf3

-- Generated from ChapterLorentzOrthochronous.lean — solution of BookProof.LorentzOrthochronous.isPO_one
import Mathlib
import Definitions.Def_ChapterLorentzOrthochronous
import Theorems.Thm_BookProof_LorentzGroup_isLorentz_one
import Definitions.Def_ChapterLorentzGroup
open BookProof.LorentzOrthochronous




open Matrix
open BookProof.LorentzGroup

set_option maxHeartbeats 1000000 in
theorem solution : IsProperOrthochronous 1 := ⟨isLorentz_one, by simp, by simp⟩
