-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.val_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:48.737264+00:00
-- url     : https://prove2.me/submissions/99a99149-6f3e-46a9-9511-4823fe3b310a

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution (L : ℝ) : val N L 0 = fun _ => 1 / L := by
  funext g; simp [val]
end FairSelling.EqualProceedsExampleFour
