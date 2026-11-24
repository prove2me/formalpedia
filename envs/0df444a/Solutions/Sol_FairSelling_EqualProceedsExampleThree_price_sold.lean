-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.price_sold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:48.13983+00:00
-- url     : https://prove2.me/submissions/0f1170e4-7329-4e11-8cbc-f4f2c38863eb

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution : ∑ g ∈ ({0} : Finset (Fin (N + 1))), price N g = 1 := by
  simp [price]
end FairSelling.EqualProceedsExampleThree
