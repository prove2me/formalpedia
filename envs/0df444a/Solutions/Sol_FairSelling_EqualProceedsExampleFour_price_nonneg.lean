-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.price_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:31:58.980739+00:00
-- url     : https://prove2.me/submissions/5c14682b-f12d-458f-b652-f4726f23c395

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
theorem _root_.solution : ∀ g, 0 ≤ price N g := fun _ => zero_le_one
end FairSelling.EqualProceedsExampleFour
