-- Prove2me | solution 1 for FairChores.FeigeNorkinChores.feigeNorkinChores_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:28:50.735297+00:00
-- url     : https://prove2.me/submissions/89d81c8d-7e74-47b5-a288-71879b6a6c6d

import Mathlib
import Definitions.Def_RequestProject_FeigeNorkinChores
import Theorems.Thm_FairChores_FeigeNorkinChores_core8C

set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.FeigeNorkinChores
namespace FairChores.FeigeNorkinChores
theorem _root_.solution (f : Fin 8 → Fin 3) :
    ∃ i : Fin 3, 380 ≤ (∑ j, if f j = i then fcW i j else 0) := by
  have h := core8C (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  simp only [costOf] at h
  rcases h with h | h | h
  · exact ⟨0, by simpa [fcW, Fin.sum_univ_eight] using h⟩
  · exact ⟨1, by simpa [fcW, Fin.sum_univ_eight] using h⟩
  · exact ⟨2, by simpa [fcW, Fin.sum_univ_eight] using h⟩
end FairChores.FeigeNorkinChores
