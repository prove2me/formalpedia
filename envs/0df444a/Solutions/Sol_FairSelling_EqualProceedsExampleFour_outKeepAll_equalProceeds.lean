-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.outKeepAll_equalProceeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:32:35.086171+00:00
-- url     : https://prove2.me/submissions/336dbc84-4985-45ea-803d-e6c1a26d8f69

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
theorem _root_.solution : (outKeepAll N).EqualProceeds (price N) := by
  intro i
  simp [outKeepAll]
end FairSelling.EqualProceedsExampleFour
