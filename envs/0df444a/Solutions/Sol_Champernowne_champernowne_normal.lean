-- Prove2me | solution 1 for Champernowne.champernowne_normal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:47:01.29863+00:00
-- url     : https://prove2.me/submissions/244333be-9661-4833-91c7-dc6c3f2afb87

module
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Definitions.Def_LeanPool_Champernowne_Main
public import Theorems.Thm_Champernowne_champPrefix_eq_map
public import Theorems.Thm_Champernowne_tendsto_countOccurrences_champPrefix_div


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b : ℕ) (hb : 2 ≤ b) :
    IsNormalSequence b (champDigit b) := by
  intro w hwne hw
  have h := tendsto_countOccurrences_champPrefix_div (b := b) (w := w) (by omega) hw hwne
  simpa only [champPrefix_eq_map] using h
end Champernowne
