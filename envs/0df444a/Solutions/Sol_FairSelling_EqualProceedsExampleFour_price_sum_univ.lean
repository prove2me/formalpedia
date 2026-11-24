-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.price_sum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:55:00.497166+00:00
-- url     : https://prove2.me/submissions/203e540f-9eea-4b55-8db2-9302da670262

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
theorem _root_.solution : ∑ g : Fin (N + 2), price N g = ((N : ℝ) + 2) := by
  simp [price]
end FairSelling.EqualProceedsExampleFour
