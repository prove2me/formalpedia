-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.val_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:23:16.244816+00:00
-- url     : https://prove2.me/submissions/8e18cad9-8ea1-4c61-a76e-890b2a47ef11

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
theorem _root_.solution : ∀ g, 0 ≤ val N g := by
  intro g; unfold val; split <;> norm_num
end FairSelling.EqualProceedsExampleThree
