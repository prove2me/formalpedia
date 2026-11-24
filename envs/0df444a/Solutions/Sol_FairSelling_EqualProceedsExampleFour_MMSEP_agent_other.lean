-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.MMSEP_agent_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:39.257485+00:00
-- url     : https://prove2.me/submissions/662b08c2-e597-468e-a816-4cab35cb726a

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_MMSEP_const
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_val_ne_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution (L : ℝ) (hL : 1 ≤ L) {i : Fin (N + 2)} (hi : i ≠ 0) :
    MMSEP (N + 2) (val N L i) (price N) = L := by
  rw [val_ne_zero N L hi, MMSEP_const N L (by linarith), max_eq_right hL]
end FairSelling.EqualProceedsExampleFour
