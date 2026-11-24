-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.price_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:49:46.290037+00:00
-- url     : https://prove2.me/submissions/512a8aff-8f64-4905-942e-d143692f6843

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
theorem _root_.solution : ∀ g, 0 ≤ price N g := by
  intro g; unfold price; split <;> norm_num
end FairSelling.EqualProceedsExampleThree
