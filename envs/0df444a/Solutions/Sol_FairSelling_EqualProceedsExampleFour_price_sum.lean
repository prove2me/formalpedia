-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.price_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:50.388037+00:00
-- url     : https://prove2.me/submissions/18791b5f-d2e4-428d-a54c-60867b9354b1

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
theorem _root_.solution (S : Finset (Fin (N + 2))) : ∑ g ∈ S, price N g = (S.card : ℝ) := by
  simp [price]
end FairSelling.EqualProceedsExampleFour
