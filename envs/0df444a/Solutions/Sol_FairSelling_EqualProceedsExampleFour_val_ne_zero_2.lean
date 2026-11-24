-- Prove2me | solution 2 for FairSelling.EqualProceedsExampleFour.val_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:24:50.566214+00:00
-- url     : https://prove2.me/submissions/a4db706d-b4ea-43cc-be6b-bf416118087d

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
theorem _root_.solution (L : ℝ) {i : Fin (N + 2)} (hi : i ≠ 0) : val N L i = fun _ => L := by
  funext g; simp [val, hi]
end FairSelling.EqualProceedsExampleFour
