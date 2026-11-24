-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.MMSEP_agent_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:38.651369+00:00
-- url     : https://prove2.me/submissions/2e0ad75e-9b42-46db-b006-bf6b111109f7

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_MMSEP_const
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_val_zero

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution (L : ℝ) (hL : 1 ≤ L) :
    MMSEP (N + 2) (val N L 0) (price N) = 1 := by
  rw [val_zero, MMSEP_const N (1 / L) (by positivity), max_eq_left]
  rw [div_le_one (by linarith)]
  exact hL
end FairSelling.EqualProceedsExampleFour
