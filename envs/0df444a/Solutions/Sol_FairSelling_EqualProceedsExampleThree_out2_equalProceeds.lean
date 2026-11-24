-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.out2_equalProceeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:30:43.086047+00:00
-- url     : https://prove2.me/submissions/f72f1f71-89d8-4f77-8634-7cea875a0149

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_price_sold

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution : (out2 N).EqualProceeds (price N) := by
  intro i
  simp only [out2, price_sold]
  push_cast
  ring
end FairSelling.EqualProceedsExampleThree
