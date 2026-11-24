-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.MMSEP_eq_MMS_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:54:56.776285+00:00
-- url     : https://prove2.me/submissions/42d4a803-61b9-4acf-8bbb-d8abed1eeaf8

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_MMS_eq
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_MMSEP_eq

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution :
    MMSEP (N + 1) (val N) (price N) = MMS (N + 1) (val N) (price N) / ((N : ℝ) + 1) := by
  rw [MMSEP_eq, MMS_eq]
end FairSelling.EqualProceedsExampleThree
