-- Prove2me | solution 1 for FairSelling.FeigeNorkin.feigeNorkin_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:21.959394+00:00
-- url     : https://prove2.me/submissions/dc6b7173-cdc2-40e3-91d4-10400d80e2a8

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkin
import Theorems.Thm_FairSelling_FeigeNorkin_core8

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.FeigeNorkin
namespace FairSelling.FeigeNorkin
theorem _root_.solution (f : Fin 8 → Fin 3) :
    ∃ i : Fin 3, (∑ j, if f j = i then fnW i j else 0) ≤ 33 := by
  have h := core8 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  simp only [valOf] at h
  rcases h with h | h | h
  · exact ⟨0, by simpa [fnW, Fin.sum_univ_eight] using h⟩
  · exact ⟨1, by simpa [fnW, Fin.sum_univ_eight] using h⟩
  · exact ⟨2, by simpa [fnW, Fin.sum_univ_eight] using h⟩
end FairSelling.FeigeNorkin
